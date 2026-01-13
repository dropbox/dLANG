//! Contract Export for Cross-Language Wiring (Phase 6.5.6)
//!
//! This module exports function contracts in a JSON format that can be
//! consumed by TypeScript tooling to verify cross-language contracts.
//!
//! The format matches what `tools/ts-contract-checker` expects.

use crate::{FunctionSpecs, MirFunction, MirType};
use serde::Serialize;
use std::collections::HashMap;
use vc_ir::{Effect, Predicate, SourceSpan};

/// Root structure for exported contracts
#[derive(Debug, Clone, Serialize)]
pub struct ContractExport {
    pub version: String,
    pub crate_name: String,
    pub timestamp: String,
    pub contracts: Vec<ExportedContract>,
    pub types: HashMap<String, ExportedType>,
}

impl ContractExport {
    /// Create a new empty contract export
    #[must_use]
    pub fn new(crate_name: &str) -> Self {
        Self {
            version: "1.0".to_string(),
            crate_name: crate_name.to_string(),
            timestamp: chrono_timestamp(),
            contracts: Vec::new(),
            types: HashMap::new(),
        }
    }

    /// Add a function's contract to the export (defaults to Public visibility)
    pub fn add_function(&mut self, func: &MirFunction, specs: &FunctionSpecs, module: &str) {
        let contract = ExportedContract::from_function(func, specs, module);
        self.contracts.push(contract);
    }

    /// Add a function's contract with explicit visibility
    pub fn add_function_with_visibility(
        &mut self,
        func: &MirFunction,
        specs: &FunctionSpecs,
        module: &str,
        visibility: Visibility,
    ) {
        let contract =
            ExportedContract::from_function_with_visibility(func, specs, module, visibility);
        self.contracts.push(contract);
    }

    /// Add a type to the export
    pub fn add_type(&mut self, name: &str, ty: ExportedType) {
        self.types.insert(name.to_string(), ty);
    }

    /// Export to JSON string
    pub fn to_json(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string_pretty(self)
    }

    /// Export to JSON string (compact)
    pub fn to_json_compact(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string(self)
    }
}

/// A single exported function contract
#[derive(Debug, Clone, Serialize)]
pub struct ExportedContract {
    pub function: String,
    pub module: String,
    pub visibility: Visibility,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub api_metadata: Option<ApiMetadata>,
    pub requires: Vec<ExportedClause>,
    pub ensures: Vec<ExportedClause>,
    pub params: Vec<ExportedParam>,
    pub return_type: String,
    pub pure: bool,
    pub effects: Vec<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub location: Option<ExportedLocation>,
}

impl ExportedContract {
    /// Create an exported contract from a MIR function and specs
    #[must_use]
    pub fn from_function(func: &MirFunction, specs: &FunctionSpecs, module: &str) -> Self {
        Self::from_function_with_visibility(func, specs, module, Visibility::Public)
    }

    /// Set API metadata (for HTTP endpoints)
    #[must_use]
    pub fn with_api_metadata(mut self, path: &str, method: &str) -> Self {
        self.api_metadata = Some(ApiMetadata {
            path: path.to_string(),
            method: method.to_string(),
        });
        self
    }

    /// Set explicit source location
    #[must_use]
    pub fn with_location(mut self, file: &str, line: u32, column: u32) -> Self {
        self.location = Some(ExportedLocation {
            file: file.to_string(),
            line,
            column,
        });
        self
    }

    /// Set location from a SourceSpan
    #[must_use]
    pub fn with_source_span(mut self, span: &SourceSpan) -> Self {
        self.location = Some(ExportedLocation::from_source_span(span));
        self
    }

    /// Create an exported contract with explicit visibility
    #[must_use]
    pub fn from_function_with_visibility(
        func: &MirFunction,
        specs: &FunctionSpecs,
        module: &str,
        visibility: Visibility,
    ) -> Self {
        let requires: Vec<ExportedClause> = specs
            .requires
            .iter()
            .map(|clause| ExportedClause {
                expr: predicate_to_string(&clause.pred),
                label: clause.label.clone(),
            })
            .collect();

        let ensures: Vec<ExportedClause> = specs
            .ensures
            .iter()
            .map(|clause| ExportedClause {
                expr: predicate_to_string(&clause.pred),
                label: clause.label.clone(),
            })
            .collect();

        let params: Vec<ExportedParam> = func
            .params
            .iter()
            .map(|(name, ty)| ExportedParam {
                name: name.clone(),
                ty: type_to_string(ty),
                refined: specs.param_refinements.get(name).cloned(),
            })
            .collect();

        let effects: Vec<String> = specs
            .effects
            .as_ref()
            .map(|eff_set| eff_set.iter().copied().map(effect_to_string).collect())
            .unwrap_or_default();

        // Extract location from the first spec clause if available
        let location = specs
            .requires
            .first()
            .or_else(|| specs.ensures.first())
            .filter(|clause| !clause.span.file.is_empty() && clause.span.line_start > 0)
            .map(|clause| ExportedLocation::from_source_span(&clause.span));

        Self {
            function: func.name.clone(),
            module: module.to_string(),
            visibility,
            api_metadata: specs.api_metadata.clone(),
            requires,
            ensures,
            params,
            return_type: type_to_string(&func.return_type),
            pure: specs.pure,
            effects,
            location,
        }
    }
}

/// API metadata for HTTP endpoints
#[derive(Debug, Clone, Serialize)]
pub struct ApiMetadata {
    pub path: String,
    pub method: String,
}

/// Visibility level
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "lowercase")]
pub enum Visibility {
    Public,
    Crate,
    Private,
}

/// A single contract clause (requires or ensures)
#[derive(Debug, Clone, Serialize)]
pub struct ExportedClause {
    pub expr: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub label: Option<String>,
}

/// A function parameter
#[derive(Debug, Clone, Serialize)]
pub struct ExportedParam {
    pub name: String,
    #[serde(rename = "type")]
    pub ty: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub refined: Option<String>,
}

/// A type definition
#[derive(Debug, Clone, Serialize)]
pub struct ExportedType {
    pub kind: TypeKind,
    pub fields: Vec<ExportedField>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub underlying: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub refined: Option<String>,
}

/// Type kind
#[derive(Debug, Clone, Serialize)]
#[serde(rename_all = "lowercase")]
pub enum TypeKind {
    Struct,
    Enum,
    Alias,
}

/// A struct field or enum variant
#[derive(Debug, Clone, Serialize)]
pub struct ExportedField {
    pub name: String,
    #[serde(rename = "type", skip_serializing_if = "Option::is_none")]
    pub ty: Option<String>,
}

/// Source location for error reporting
#[derive(Debug, Clone, Serialize)]
pub struct ExportedLocation {
    pub file: String,
    pub line: u32,
    pub column: u32,
}

impl ExportedLocation {
    /// Create from a SourceSpan
    #[must_use]
    pub fn from_source_span(span: &SourceSpan) -> Self {
        Self {
            file: span.file.to_string(),
            line: span.line_start,
            column: span.col_start,
        }
    }
}

/// Convert a MirType to a string representation
fn type_to_string(ty: &MirType) -> String {
    ty.to_string()
}

/// Convert a Predicate to a string representation
fn predicate_to_string(pred: &Predicate) -> String {
    pred.to_string()
}

/// Convert an Effect to a string
fn effect_to_string(effect: Effect) -> String {
    effect.as_str().to_string()
}

/// Get current timestamp in ISO 8601 format
fn chrono_timestamp() -> String {
    use std::time::{SystemTime, UNIX_EPOCH};

    let now = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default();

    // Convert to seconds and format as ISO 8601
    let secs = now.as_secs();

    // Calculate date/time components
    // Days since Unix epoch (1970-01-01)
    let days = secs / 86400;
    let remaining_secs = secs % 86400;
    let hours = remaining_secs / 3600;
    let minutes = (remaining_secs % 3600) / 60;
    let seconds = remaining_secs % 60;

    // Simple date calculation (good enough for 2000-2099)
    let mut year = 1970;
    let mut remaining_days = days as i64;

    // Advance years
    loop {
        let days_in_year = if is_leap_year(year) { 366 } else { 365 };
        if remaining_days < days_in_year {
            break;
        }
        remaining_days -= days_in_year;
        year += 1;
    }

    // Advance months
    let mut month = 1;
    loop {
        let days_in_month = days_in_month(year, month);
        if remaining_days < i64::from(days_in_month) {
            break;
        }
        remaining_days -= i64::from(days_in_month);
        month += 1;
    }

    let day = remaining_days + 1;

    format!("{year:04}-{month:02}-{day:02}T{hours:02}:{minutes:02}:{seconds:02}Z")
}

/// Check if a year is a leap year
const fn is_leap_year(year: i64) -> bool {
    (year % 4 == 0 && year % 100 != 0) || (year % 400 == 0)
}

/// Get the number of days in a month
const fn days_in_month(year: i64, month: u32) -> u32 {
    match month {
        // Months with 31 days
        1 | 3 | 5 | 7 | 8 | 10 | 12 => 31,
        // February (leap year aware)
        2 => {
            if is_leap_year(year) {
                29
            } else {
                28
            }
        }
        // Months with 30 days (4, 6, 9, 11) and fallback
        _ => 30,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use vc_ir::{EffectSet, Expr, SourceSpan, SpecClause};

    fn make_test_function() -> MirFunction {
        MirFunction {
            name: "create_user".to_string(),
            params: vec![
                (
                    "email".to_string(),
                    MirType::Adt {
                        name: "String".to_string(),
                    },
                ),
                (
                    "age".to_string(),
                    MirType::Int {
                        signed: false,
                        bits: 32,
                    },
                ),
            ],
            return_type: MirType::Adt {
                name: "User".to_string(),
            },
            blocks: vec![],
            locals: vec![],
            span: SourceSpan::default(),
        }
    }

    fn make_test_specs() -> FunctionSpecs {
        // Use Predicate::Expr with comparison expression
        let age_gt_18 = Predicate::Expr(Expr::Gt(
            Box::new(Expr::Var("age".to_string())),
            Box::new(Expr::IntLit(18)),
        ));
        let result_id_gt_0 = Predicate::Expr(Expr::Gt(
            Box::new(Expr::StructField(
                Box::new(Expr::Var("result".to_string())),
                "id".to_string(),
            )),
            Box::new(Expr::IntLit(0)),
        ));

        FunctionSpecs {
            requires: vec![SpecClause {
                pred: age_gt_18,
                span: SourceSpan::dummy(),
                label: Some("user must be adult".to_string()),
            }],
            ensures: vec![SpecClause {
                pred: result_id_gt_0,
                span: SourceSpan::dummy(),
                label: None,
            }],
            decreases: None,
            pure: false,
            trusted: false,
            api_metadata: None,
            effects: Some(EffectSet::from_effects(vec![Effect::IO])),
            param_refinements: HashMap::default(),
        }
    }

    #[test]
    fn test_contract_export_basic() {
        let mut export = ContractExport::new("my_api");
        let func = make_test_function();
        let specs = make_test_specs();

        export.add_function(&func, &specs, "api::users");

        assert_eq!(export.crate_name, "my_api");
        assert_eq!(export.contracts.len(), 1);

        let contract = &export.contracts[0];
        assert_eq!(contract.function, "create_user");
        assert_eq!(contract.module, "api::users");
        assert_eq!(contract.params.len(), 2);
        assert_eq!(contract.requires.len(), 1);
        assert_eq!(contract.ensures.len(), 1);
        assert!(!contract.pure);
        assert_eq!(contract.effects.len(), 1);
        assert_eq!(contract.effects[0], "IO");
    }

    #[test]
    fn test_contract_export_predicate_strings() {
        let mut export = ContractExport::new("my_api");
        let func = make_test_function();
        let specs = make_test_specs();

        export.add_function(&func, &specs, "api::users");
        let contract = &export.contracts[0];

        assert_eq!(contract.requires.len(), 1);
        assert_eq!(contract.requires[0].expr, "age > 18");

        assert_eq!(contract.ensures.len(), 1);
        assert_eq!(contract.ensures[0].expr, "result.id > 0");
    }

    #[test]
    fn test_contract_export_json() {
        let mut export = ContractExport::new("test_crate");
        let func = make_test_function();
        let specs = make_test_specs();

        export.add_function(&func, &specs, "api");

        let json = export.to_json().expect("JSON serialization failed");
        assert!(json.contains("\"version\": \"1.0\""));
        assert!(json.contains("\"crate_name\": \"test_crate\""));
        assert!(json.contains("\"function\": \"create_user\""));
        assert!(json.contains("\"user must be adult\""));
    }

    #[test]
    fn test_pure_function_export() {
        let func = MirFunction {
            name: "add".to_string(),
            params: vec![
                (
                    "a".to_string(),
                    MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                ),
                (
                    "b".to_string(),
                    MirType::Int {
                        signed: true,
                        bits: 32,
                    },
                ),
            ],
            return_type: MirType::Int {
                signed: true,
                bits: 32,
            },
            blocks: vec![],
            locals: vec![],
            span: SourceSpan::default(),
        };

        let specs = FunctionSpecs {
            requires: vec![],
            ensures: vec![],
            decreases: None,
            pure: true,
            trusted: false,
            api_metadata: None,
            effects: None,
            param_refinements: HashMap::default(),
        };

        let mut export = ContractExport::new("math");
        export.add_function(&func, &specs, "math");

        let contract = &export.contracts[0];
        assert!(contract.pure);
        assert!(contract.effects.is_empty());
    }

    #[test]
    fn test_type_export() {
        let mut export = ContractExport::new("types");

        export.add_type(
            "User",
            ExportedType {
                kind: TypeKind::Struct,
                fields: vec![
                    ExportedField {
                        name: "id".to_string(),
                        ty: Some("u64".to_string()),
                    },
                    ExportedField {
                        name: "email".to_string(),
                        ty: Some("String".to_string()),
                    },
                ],
                underlying: None,
                refined: None,
            },
        );

        assert!(export.types.contains_key("User"));
        let user_type = &export.types["User"];
        assert_eq!(user_type.fields.len(), 2);
    }

    #[test]
    fn test_chrono_timestamp_format() {
        let ts = chrono_timestamp();

        // Verify ISO 8601 format: YYYY-MM-DDTHH:MM:SSZ
        assert!(ts.len() == 20, "Timestamp should be 20 chars: {ts}");
        assert!(ts.ends_with('Z'), "Timestamp should end with Z: {ts}");
        assert!(ts.chars().nth(4) == Some('-'), "Position 4 should be '-'");
        assert!(ts.chars().nth(7) == Some('-'), "Position 7 should be '-'");
        assert!(ts.chars().nth(10) == Some('T'), "Position 10 should be 'T'");
        assert!(ts.chars().nth(13) == Some(':'), "Position 13 should be ':'");
        assert!(ts.chars().nth(16) == Some(':'), "Position 16 should be ':'");

        // Verify year is reasonable (2020-2100)
        let year: u32 = ts[0..4].parse().expect("Year should be numeric");
        assert!((2020..=2100).contains(&year), "Year {year} out of range");
    }

    #[test]
    fn test_is_leap_year() {
        assert!(is_leap_year(2000)); // Divisible by 400
        assert!(is_leap_year(2024)); // Divisible by 4, not 100
        assert!(!is_leap_year(1900)); // Divisible by 100, not 400
        assert!(!is_leap_year(2023)); // Not divisible by 4
    }

    #[test]
    fn test_days_in_month() {
        assert_eq!(days_in_month(2024, 1), 31); // January
        assert_eq!(days_in_month(2024, 2), 29); // February leap year
        assert_eq!(days_in_month(2023, 2), 28); // February non-leap
        assert_eq!(days_in_month(2024, 4), 30); // April
        assert_eq!(days_in_month(2024, 12), 31); // December
    }

    #[test]
    fn test_visibility_export() {
        let func = make_test_function();
        let specs = make_test_specs();
        let mut export = ContractExport::new("test_crate");

        // Test public (default)
        export.add_function(&func, &specs, "public_mod");
        assert!(matches!(export.contracts[0].visibility, Visibility::Public));

        // Test crate visibility
        export.add_function_with_visibility(&func, &specs, "crate_mod", Visibility::Crate);
        assert!(matches!(export.contracts[1].visibility, Visibility::Crate));

        // Test private visibility
        export.add_function_with_visibility(&func, &specs, "private_mod", Visibility::Private);
        assert!(matches!(
            export.contracts[2].visibility,
            Visibility::Private
        ));

        // Verify JSON serialization
        let json = export.to_json().expect("JSON serialization failed");
        assert!(json.contains("\"public\""));
        assert!(json.contains("\"crate\""));
        assert!(json.contains("\"private\""));
    }

    #[test]
    fn test_source_location_extraction() {
        use std::sync::Arc;

        let func = make_test_function();

        // Create specs with a real source span
        let age_gt_18 = Predicate::Expr(Expr::Gt(
            Box::new(Expr::Var("age".to_string())),
            Box::new(Expr::IntLit(18)),
        ));
        let real_span = SourceSpan {
            file: Arc::from("src/api/users.rs"),
            line_start: 42,
            line_end: 42,
            col_start: 5,
            col_end: 30,
        };
        let specs = FunctionSpecs {
            requires: vec![SpecClause {
                pred: age_gt_18,
                span: real_span,
                label: None,
            }],
            ensures: vec![],
            decreases: None,
            pure: false,
            trusted: false,
            api_metadata: None,
            effects: None,
            param_refinements: HashMap::default(),
        };

        let mut export = ContractExport::new("test_crate");
        export.add_function(&func, &specs, "api::users");

        // Location should be extracted from the spec clause
        let contract = &export.contracts[0];
        assert!(contract.location.is_some(), "Location should be present");
        let loc = contract.location.as_ref().unwrap();
        assert_eq!(loc.file, "src/api/users.rs");
        assert_eq!(loc.line, 42);
        assert_eq!(loc.column, 5);

        // Verify JSON contains location
        let json = export.to_json().expect("JSON serialization failed");
        assert!(json.contains("\"file\": \"src/api/users.rs\""));
        assert!(json.contains("\"line\": 42"));
    }

    #[test]
    fn test_api_metadata_builder() {
        let func = make_test_function();
        let specs = FunctionSpecs::default();

        let contract = ExportedContract::from_function(&func, &specs, "api")
            .with_api_metadata("/api/users", "POST");

        assert!(contract.api_metadata.is_some());
        let meta = contract.api_metadata.as_ref().unwrap();
        assert_eq!(meta.path, "/api/users");
        assert_eq!(meta.method, "POST");
    }

    #[test]
    fn test_api_metadata_extracted_from_specs() {
        let func = make_test_function();
        let specs = FunctionSpecs {
            api_metadata: Some(ApiMetadata {
                path: "/api/users".to_string(),
                method: "POST".to_string(),
            }),
            ..Default::default()
        };

        let contract = ExportedContract::from_function(&func, &specs, "api");

        let meta = contract.api_metadata.as_ref().unwrap();
        assert_eq!(meta.path, "/api/users");
        assert_eq!(meta.method, "POST");
    }

    #[test]
    fn test_param_refinements_extracted_from_specs() {
        let func = make_test_function();
        let mut specs = FunctionSpecs::default();
        specs
            .param_refinements
            .insert("age".to_string(), "age >= 18".to_string());

        let contract = ExportedContract::from_function(&func, &specs, "api");

        let email = contract.params.iter().find(|p| p.name == "email").unwrap();
        assert!(email.refined.is_none());

        let age = contract.params.iter().find(|p| p.name == "age").unwrap();
        assert_eq!(age.refined.as_deref(), Some("age >= 18"));
    }

    #[test]
    fn test_location_builder() {
        let func = make_test_function();
        let specs = FunctionSpecs::default();

        let contract = ExportedContract::from_function(&func, &specs, "api").with_location(
            "src/main.rs",
            100,
            8,
        );

        assert!(contract.location.is_some());
        let loc = contract.location.as_ref().unwrap();
        assert_eq!(loc.file, "src/main.rs");
        assert_eq!(loc.line, 100);
        assert_eq!(loc.column, 8);
    }

    #[test]
    fn test_exported_location_from_source_span() {
        use std::sync::Arc;

        let span = SourceSpan {
            file: Arc::from("lib.rs"),
            line_start: 25,
            line_end: 30,
            col_start: 4,
            col_end: 50,
        };

        let loc = ExportedLocation::from_source_span(&span);
        assert_eq!(loc.file, "lib.rs");
        assert_eq!(loc.line, 25);
        assert_eq!(loc.column, 4);
    }
}
