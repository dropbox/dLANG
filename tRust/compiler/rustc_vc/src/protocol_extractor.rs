//! Protocol Module Extractor (Phase 6.3)
//!
//! Extracts protocol specifications from Rust modules annotated with `#[protocol]`.
//! The extractor parses module structure, identifies state variables, actions,
//! safety/liveness properties, and fairness conditions.

use vc_ir::{
    temporal::{
        Action, FairnessCondition, ModelCheckConfig, ProtocolExtractionError,
        ProtocolExtractionErrorKind, ProtocolExtractionResult, ProtocolMessage, ProtocolModule,
        ProtocolParty, StateVariable, TemporalFormula,
    },
    Expr, Predicate, SourceSpan, VcType,
};

/// Configuration options for protocol extraction
#[derive(Debug, Clone, Default)]
pub struct ProtocolExtractorOptions {
    /// Whether to infer state variables from struct definitions
    pub infer_state_variables: bool,

    /// Whether to infer actions from function definitions
    pub infer_actions: bool,

    /// Whether to require an init function
    pub require_init: bool,

    /// Default model checking configuration
    pub default_model_check_config: Option<ModelCheckConfig>,
}

impl ProtocolExtractorOptions {
    /// Create options with strict validation
    #[must_use]
    pub const fn strict() -> Self {
        Self {
            infer_state_variables: false,
            infer_actions: false,
            require_init: true,
            default_model_check_config: None,
        }
    }

    /// Create options with inference enabled
    #[must_use]
    pub const fn with_inference() -> Self {
        Self {
            infer_state_variables: true,
            infer_actions: true,
            require_init: false,
            default_model_check_config: Some(ModelCheckConfig {
                max_depth: 100,
                state_bound: Some(10000),
                symmetry: vec![],
                workers: 4,
            }),
        }
    }
}

/// Protocol extractor that parses module structure
pub struct ProtocolExtractor {
    options: ProtocolExtractorOptions,
    errors: Vec<ProtocolExtractionError>,
    warnings: Vec<String>,
}

impl ProtocolExtractor {
    /// Create a new extractor with default options
    #[must_use]
    pub fn new() -> Self {
        Self {
            options: ProtocolExtractorOptions::default(),
            errors: Vec::new(),
            warnings: Vec::new(),
        }
    }

    /// Create a new extractor with custom options
    #[must_use]
    pub const fn with_options(options: ProtocolExtractorOptions) -> Self {
        Self {
            options,
            errors: Vec::new(),
            warnings: Vec::new(),
        }
    }

    /// Extract a protocol from a module definition
    pub fn extract(&mut self, module_def: &ModuleDefinition) -> ProtocolExtractionResult {
        self.errors.clear();
        self.warnings.clear();

        // Check if module has #[protocol] attribute
        if !module_def.has_protocol_attr {
            self.add_error(
                ProtocolExtractionErrorKind::NotAProtocol,
                format!(
                    "Module '{}' is not marked with #[protocol]",
                    module_def.name
                ),
                module_def.span.clone(),
            );
            return ProtocolExtractionResult::failure(self.errors.clone());
        }

        let mut protocol_module = ProtocolModule::new(&module_def.name);

        // Set protocol name from attribute if provided
        if let Some(name) = &module_def.protocol_name {
            protocol_module = protocol_module.with_protocol_name(name);
        }

        // Set source information
        protocol_module
            .source_path
            .clone_from(&module_def.source_path);
        protocol_module.source_span.clone_from(&module_def.span);

        // Extract state variables from struct definitions
        for struct_def in &module_def.structs {
            Self::extract_state_variables(&mut protocol_module, struct_def);
        }

        // Extract init function
        let mut has_init = false;
        for func_def in &module_def.functions {
            if func_def.is_init {
                has_init = true;
                self.extract_init(&mut protocol_module, func_def);
            }
        }

        if !has_init && self.options.require_init {
            self.add_error(
                ProtocolExtractionErrorKind::MissingInit,
                format!(
                    "Protocol '{}' requires an init function marked with #[init]",
                    module_def.name
                ),
                module_def.span.clone(),
            );
        }

        // Extract actions
        for func_def in &module_def.functions {
            if func_def.is_action {
                Self::extract_action(&mut protocol_module, func_def);
            }
        }

        // Extract safety properties
        for func_def in &module_def.functions {
            if func_def.is_safety {
                self.extract_safety(&mut protocol_module, func_def);
            }
        }

        // Extract liveness properties
        for func_def in &module_def.functions {
            if func_def.is_liveness {
                self.extract_liveness(&mut protocol_module, func_def);
            }
        }

        // Extract fairness conditions
        for func_def in &module_def.functions {
            if let Some(action) = &func_def.weak_fairness {
                protocol_module.add_fairness(FairnessCondition::Weak(action.clone()));
            }
            if let Some(action) = &func_def.strong_fairness {
                protocol_module.add_fairness(FairnessCondition::Strong(action.clone()));
            }
        }

        // Extract parties (multi-party protocols)
        for sub_module in &module_def.sub_modules {
            if sub_module.is_party {
                Self::extract_party(&mut protocol_module, sub_module);
            }
        }

        // Extract messages (multi-party protocols)
        for struct_def in &module_def.structs {
            if let Some(msg_spec) = &struct_def.message_spec {
                Self::extract_message(&mut protocol_module, struct_def, msg_spec);
            }
        }

        // Set model check config
        protocol_module
            .model_check_config
            .clone_from(&self.options.default_model_check_config);

        // Validate the extracted protocol
        if let Err(e) = protocol_module.validate() {
            self.add_error(
                ProtocolExtractionErrorKind::ParseError,
                format!("Protocol validation failed: {e}"),
                module_def.span.clone(),
            );
        }

        // Build result
        let mut result = if self.errors.is_empty() {
            ProtocolExtractionResult::success(protocol_module)
        } else {
            ProtocolExtractionResult::failure(self.errors.clone())
        };

        for warning in &self.warnings {
            result.add_warning(warning);
        }

        result
    }

    fn extract_state_variables(module: &mut ProtocolModule, struct_def: &StructDefinition) {
        for field in &struct_def.fields {
            let var = StateVariable {
                name: field.name.clone(),
                ty: field.ty.clone(),
                type_invariant: field.type_invariant.clone(),
            };
            module.add_variable(var);
        }
    }

    fn extract_init(&mut self, module: &mut ProtocolModule, func_def: &FunctionDefinition) {
        // In a real implementation, this would analyze the function body
        // to extract the initial state predicate.
        // For now, we create a placeholder predicate based on the function name.
        if let Some(init_pred) = &func_def.init_predicate {
            module.set_init(init_pred.clone());
        } else {
            // Default: use function name as init indicator
            self.warnings.push(format!(
                "Init function '{}' has no explicit predicate; using default",
                func_def.name
            ));
        }
    }

    fn extract_action(module: &mut ProtocolModule, func_def: &FunctionDefinition) {
        let action_name = func_def.action_name.as_ref().unwrap_or(&func_def.name);

        let action = Action {
            name: action_name.clone(),
            enabled: func_def.enabled.clone().unwrap_or(Predicate::Bool(true)),
            effect: func_def.effect.clone(),
        };

        module.add_action(action);
    }

    fn extract_safety(&mut self, module: &mut ProtocolModule, func_def: &FunctionDefinition) {
        // Safety property: □P (always P)
        // The function body defines P
        if let Some(pred) = &func_def.safety_predicate {
            let formula = TemporalFormula::always(TemporalFormula::State(pred.clone()));
            module.add_safety(formula);
        } else {
            self.warnings.push(format!(
                "Safety function '{}' has no explicit predicate",
                func_def.name
            ));
        }
    }

    fn extract_liveness(&mut self, module: &mut ProtocolModule, func_def: &FunctionDefinition) {
        // Liveness property: ◇P (eventually P)
        if let Some(pred) = &func_def.liveness_predicate {
            let formula = TemporalFormula::eventually(TemporalFormula::State(pred.clone()));
            module.add_liveness(formula);
        } else {
            self.warnings.push(format!(
                "Liveness function '{}' has no explicit predicate",
                func_def.name
            ));
        }
    }

    fn extract_party(module: &mut ProtocolModule, sub_module: &ModuleDefinition) {
        let mut party = ProtocolParty::new(&sub_module.name);

        // Extract local variables from party's structs
        for struct_def in &sub_module.structs {
            for field in &struct_def.fields {
                party.add_variable(StateVariable {
                    name: field.name.clone(),
                    ty: field.ty.clone(),
                    type_invariant: field.type_invariant.clone(),
                });
            }
        }

        // Extract party's actions
        for func_def in &sub_module.functions {
            if func_def.is_action {
                let action_name = func_def.action_name.as_ref().unwrap_or(&func_def.name);
                party.add_action(action_name);
            }
        }

        module.add_party(party);
    }

    fn extract_message(
        module: &mut ProtocolModule,
        struct_def: &StructDefinition,
        msg_spec: &MessageSpec,
    ) {
        let mut message = ProtocolMessage::new(&struct_def.name, &msg_spec.from, &msg_spec.to);

        for field in &struct_def.fields {
            message.add_field(&field.name, field.ty.clone());
        }

        if let Some(guard) = &msg_spec.send_guard {
            message.set_send_guard(guard.clone());
        }

        module.add_message(message);
    }

    fn add_error(
        &mut self,
        kind: ProtocolExtractionErrorKind,
        message: String,
        span: Option<SourceSpan>,
    ) {
        self.errors.push(ProtocolExtractionError {
            kind,
            message,
            span,
        });
    }
}

impl Default for ProtocolExtractor {
    fn default() -> Self {
        Self::new()
    }
}

/// Statistics about protocol extraction
#[derive(Debug, Clone, Default)]
pub struct ProtocolExtractorStats {
    pub modules_processed: usize,
    pub protocols_extracted: usize,
    pub total_variables: usize,
    pub total_actions: usize,
    pub total_safety_properties: usize,
    pub total_liveness_properties: usize,
    pub total_parties: usize,
    pub total_messages: usize,
    pub total_errors: usize,
    pub total_warnings: usize,
}

impl ProtocolExtractorStats {
    /// Create new stats
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Update stats from an extraction result
    pub const fn update_from_result(&mut self, result: &ProtocolExtractionResult) {
        self.modules_processed += 1;

        if let Some(module) = &result.module {
            self.protocols_extracted += 1;
            self.total_variables += module.variable_count();
            self.total_actions += module.action_count();
            self.total_safety_properties += module.safety_count();
            self.total_liveness_properties += module.liveness_count();
            self.total_parties += module.parties.len();
            self.total_messages += module.messages.len();
        }

        self.total_errors += result.errors.len();
        self.total_warnings += result.warnings.len();
    }
}

// ============================================
// Module Definition Types for Extraction
// ============================================

/// Represents a parsed Rust module for protocol extraction
#[derive(Debug, Clone)]
pub struct ModuleDefinition {
    /// Module name
    pub name: String,

    /// Whether the module has `#[protocol]` attribute
    pub has_protocol_attr: bool,

    /// Protocol name from #[protocol(name = "...")]
    pub protocol_name: Option<String>,

    /// Source file path
    pub source_path: Option<String>,

    /// Source span
    pub span: Option<SourceSpan>,

    /// Struct definitions in the module
    pub structs: Vec<StructDefinition>,

    /// Function definitions in the module
    pub functions: Vec<FunctionDefinition>,

    /// Sub-modules (for multi-party protocols)
    pub sub_modules: Vec<ModuleDefinition>,

    /// Whether this is a party module
    pub is_party: bool,
}

impl ModuleDefinition {
    /// Create a new module definition
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            has_protocol_attr: false,
            protocol_name: None,
            source_path: None,
            span: None,
            structs: Vec::new(),
            functions: Vec::new(),
            sub_modules: Vec::new(),
            is_party: false,
        }
    }

    /// Mark as a protocol module
    #[must_use]
    pub const fn as_protocol(mut self) -> Self {
        self.has_protocol_attr = true;
        self
    }

    /// Set protocol name
    #[must_use]
    pub fn with_protocol_name(mut self, name: impl Into<String>) -> Self {
        self.protocol_name = Some(name.into());
        self
    }

    /// Add a struct definition
    pub fn add_struct(&mut self, struct_def: StructDefinition) {
        self.structs.push(struct_def);
    }

    /// Add a function definition
    pub fn add_function(&mut self, func_def: FunctionDefinition) {
        self.functions.push(func_def);
    }

    /// Add a sub-module
    pub fn add_sub_module(&mut self, sub_module: Self) {
        self.sub_modules.push(sub_module);
    }
}

/// Represents a struct definition for state variables
#[derive(Debug, Clone)]
pub struct StructDefinition {
    /// Struct name
    pub name: String,

    /// Fields
    pub fields: Vec<FieldDefinition>,

    /// Message spec if this is a `#[message]` struct
    pub message_spec: Option<MessageSpec>,
}

impl StructDefinition {
    /// Create a new struct definition
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            fields: Vec::new(),
            message_spec: None,
        }
    }

    /// Add a field
    pub fn add_field(&mut self, field: FieldDefinition) {
        self.fields.push(field);
    }
}

/// Represents a struct field
#[derive(Debug, Clone)]
pub struct FieldDefinition {
    /// Field name
    pub name: String,

    /// Field type
    pub ty: VcType,

    /// Type invariant (if specified)
    pub type_invariant: Option<Predicate>,
}

impl FieldDefinition {
    /// Create a new field definition
    pub fn new(name: impl Into<String>, ty: VcType) -> Self {
        Self {
            name: name.into(),
            ty,
            type_invariant: None,
        }
    }

    /// Set type invariant
    #[must_use]
    pub fn with_invariant(mut self, invariant: Predicate) -> Self {
        self.type_invariant = Some(invariant);
        self
    }
}

/// Represents a function definition
#[derive(Debug, Clone)]
pub struct FunctionDefinition {
    /// Function name
    pub name: String,

    /// Whether this is an `#[init]` function
    pub is_init: bool,

    /// Whether this is an `#[action]` function
    pub is_action: bool,

    /// Action name (from #[action(name = "...")])
    pub action_name: Option<String>,

    /// Whether this is a `#[safety]` function
    pub is_safety: bool,

    /// Whether this is a `#[liveness]` function
    pub is_liveness: bool,

    /// Weak fairness action (from #[weak_fairness(action)])
    pub weak_fairness: Option<String>,

    /// Strong fairness action (from #[strong_fairness(action)])
    pub strong_fairness: Option<String>,

    /// Init predicate (extracted from function body)
    pub init_predicate: Option<Predicate>,

    /// Enabled predicate for actions
    pub enabled: Option<Predicate>,

    /// Effect of action (variable updates)
    pub effect: Vec<(String, Expr)>,

    /// Safety predicate (for `#[safety]` functions)
    pub safety_predicate: Option<Predicate>,

    /// Liveness predicate (for `#[liveness]` functions)
    pub liveness_predicate: Option<Predicate>,
}

impl FunctionDefinition {
    /// Create a new function definition
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            is_init: false,
            is_action: false,
            action_name: None,
            is_safety: false,
            is_liveness: false,
            weak_fairness: None,
            strong_fairness: None,
            init_predicate: None,
            enabled: None,
            effect: Vec::new(),
            safety_predicate: None,
            liveness_predicate: None,
        }
    }

    /// Mark as init function
    #[must_use]
    pub const fn as_init(mut self) -> Self {
        self.is_init = true;
        self
    }

    /// Mark as action function
    #[must_use]
    pub const fn as_action(mut self) -> Self {
        self.is_action = true;
        self
    }

    /// Set action name
    #[must_use]
    pub fn with_action_name(mut self, name: impl Into<String>) -> Self {
        self.action_name = Some(name.into());
        self
    }

    /// Mark as safety function
    #[must_use]
    pub const fn as_safety(mut self) -> Self {
        self.is_safety = true;
        self
    }

    /// Mark as liveness function
    #[must_use]
    pub const fn as_liveness(mut self) -> Self {
        self.is_liveness = true;
        self
    }

    /// Set init predicate
    #[must_use]
    pub fn with_init_predicate(mut self, pred: Predicate) -> Self {
        self.init_predicate = Some(pred);
        self
    }

    /// Set enabled predicate
    #[must_use]
    pub fn with_enabled(mut self, pred: Predicate) -> Self {
        self.enabled = Some(pred);
        self
    }

    /// Add effect
    pub fn add_effect(&mut self, var: impl Into<String>, expr: Expr) {
        self.effect.push((var.into(), expr));
    }

    /// Set safety predicate
    #[must_use]
    pub fn with_safety_predicate(mut self, pred: Predicate) -> Self {
        self.safety_predicate = Some(pred);
        self
    }

    /// Set liveness predicate
    #[must_use]
    pub fn with_liveness_predicate(mut self, pred: Predicate) -> Self {
        self.liveness_predicate = Some(pred);
        self
    }
}

/// Message specification from #[message(from = "...", to = "...")]
#[derive(Debug, Clone)]
pub struct MessageSpec {
    /// Sender party
    pub from: String,

    /// Receiver party
    pub to: String,

    /// Send guard predicate
    pub send_guard: Option<Predicate>,
}

impl MessageSpec {
    /// Create a new message spec
    pub fn new(from: impl Into<String>, to: impl Into<String>) -> Self {
        Self {
            from: from.into(),
            to: to.into(),
            send_guard: None,
        }
    }
}

// ============================================
// Unit Tests
// ============================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_extractor_new() {
        let extractor = ProtocolExtractor::new();
        assert!(extractor.errors.is_empty());
        assert!(extractor.warnings.is_empty());
    }

    #[test]
    fn test_extractor_options_strict() {
        let options = ProtocolExtractorOptions::strict();
        assert!(!options.infer_state_variables);
        assert!(!options.infer_actions);
        assert!(options.require_init);
    }

    #[test]
    fn test_extractor_options_with_inference() {
        let options = ProtocolExtractorOptions::with_inference();
        assert!(options.infer_state_variables);
        assert!(options.infer_actions);
        assert!(!options.require_init);
        assert!(options.default_model_check_config.is_some());
    }

    #[test]
    fn test_extract_not_a_protocol() {
        let mut extractor = ProtocolExtractor::new();
        let module_def = ModuleDefinition::new("test_module");

        let result = extractor.extract(&module_def);
        assert!(!result.is_success());
        assert_eq!(result.errors.len(), 1);
        assert!(matches!(
            result.errors[0].kind,
            ProtocolExtractionErrorKind::NotAProtocol
        ));
    }

    #[test]
    fn test_extract_simple_protocol() {
        let mut extractor =
            ProtocolExtractor::with_options(ProtocolExtractorOptions::with_inference());

        let mut module_def = ModuleDefinition::new("counter").as_protocol();

        // Add state struct
        let mut state_struct = StructDefinition::new("State");
        state_struct.add_field(FieldDefinition::new(
            "count",
            VcType::Int {
                signed: true,
                bits: 32,
            },
        ));
        module_def.add_struct(state_struct);

        // Add init function: count == 0
        let init_fn = FunctionDefinition::new("init")
            .as_init()
            .with_init_predicate(Predicate::Expr(Expr::Eq(
                Box::new(Expr::Var("count".to_string())),
                Box::new(Expr::IntLit(0)),
            )));
        module_def.add_function(init_fn);

        // Add action: count' = count + 1
        let mut action_fn = FunctionDefinition::new("increment").as_action();
        action_fn.add_effect(
            "count",
            Expr::Add(
                Box::new(Expr::Var("count".to_string())),
                Box::new(Expr::IntLit(1)),
            ),
        );
        module_def.add_function(action_fn);

        let result = extractor.extract(&module_def);
        assert!(result.is_success());

        let module = result.module.unwrap();
        assert_eq!(module.name, "counter");
        assert_eq!(module.variable_count(), 1);
        assert_eq!(module.action_count(), 1);
    }

    #[test]
    fn test_extract_protocol_with_properties() {
        let mut extractor =
            ProtocolExtractor::with_options(ProtocolExtractorOptions::with_inference());

        let mut module_def = ModuleDefinition::new("mutex")
            .as_protocol()
            .with_protocol_name("MutualExclusion");

        // Add state struct
        let mut state_struct = StructDefinition::new("State");
        state_struct.add_field(FieldDefinition::new("in_critical_a", VcType::Bool));
        state_struct.add_field(FieldDefinition::new("in_critical_b", VcType::Bool));
        module_def.add_struct(state_struct);

        // Add init function: !in_critical_a && !in_critical_b
        let init_fn = FunctionDefinition::new("init")
            .as_init()
            .with_init_predicate(Predicate::And(vec![
                Predicate::Not(Box::new(Predicate::Expr(Expr::Var(
                    "in_critical_a".to_string(),
                )))),
                Predicate::Not(Box::new(Predicate::Expr(Expr::Var(
                    "in_critical_b".to_string(),
                )))),
            ]));
        module_def.add_function(init_fn);

        // Add safety property: !(in_critical_a && in_critical_b)
        let safety_fn = FunctionDefinition::new("mutex_exclusion")
            .as_safety()
            .with_safety_predicate(Predicate::Not(Box::new(Predicate::And(vec![
                Predicate::Expr(Expr::Var("in_critical_a".to_string())),
                Predicate::Expr(Expr::Var("in_critical_b".to_string())),
            ]))));
        module_def.add_function(safety_fn);

        let result = extractor.extract(&module_def);
        assert!(result.is_success());

        let module = result.module.unwrap();
        assert_eq!(module.protocol.name, "MutualExclusion");
        assert_eq!(module.variable_count(), 2);
        assert_eq!(module.safety_count(), 1);
    }

    #[test]
    fn test_extract_multi_party_protocol() {
        let mut extractor =
            ProtocolExtractor::with_options(ProtocolExtractorOptions::with_inference());

        let mut module_def = ModuleDefinition::new("client_server").as_protocol();

        // Add client party
        let mut client_module = ModuleDefinition::new("client");
        client_module.is_party = true;
        let mut client_state = StructDefinition::new("ClientState");
        client_state.add_field(FieldDefinition::new("request_sent", VcType::Bool));
        client_module.add_struct(client_state);

        let send_action = FunctionDefinition::new("send_request").as_action();
        client_module.add_function(send_action);
        module_def.add_sub_module(client_module);

        // Add server party
        let mut server_module = ModuleDefinition::new("server");
        server_module.is_party = true;
        let mut server_state = StructDefinition::new("ServerState");
        server_state.add_field(FieldDefinition::new("request_received", VcType::Bool));
        server_module.add_struct(server_state);

        let handle_action = FunctionDefinition::new("handle_request").as_action();
        server_module.add_function(handle_action);
        module_def.add_sub_module(server_module);

        // Add message type
        let mut request_struct = StructDefinition::new("Request");
        request_struct.add_field(FieldDefinition::new(
            "payload",
            VcType::Int {
                signed: true,
                bits: 32,
            },
        ));
        request_struct.message_spec = Some(MessageSpec::new("client", "server"));
        module_def.add_struct(request_struct);

        let result = extractor.extract(&module_def);
        assert!(result.is_success());

        let module = result.module.unwrap();
        assert!(module.is_multi_party());
        assert_eq!(module.parties.len(), 2);
        assert_eq!(module.messages.len(), 1);
    }

    #[test]
    fn test_extract_with_fairness() {
        let mut extractor =
            ProtocolExtractor::with_options(ProtocolExtractorOptions::with_inference());

        let mut module_def = ModuleDefinition::new("scheduler").as_protocol();

        // Add action
        let action_fn = FunctionDefinition::new("schedule").as_action();
        module_def.add_function(action_fn);

        // Add weak fairness
        let mut wf_fn = FunctionDefinition::new("wf_schedule");
        wf_fn.weak_fairness = Some("schedule".to_string());
        module_def.add_function(wf_fn);

        // Add strong fairness
        let mut sf_fn = FunctionDefinition::new("sf_schedule");
        sf_fn.strong_fairness = Some("schedule".to_string());
        module_def.add_function(sf_fn);

        let result = extractor.extract(&module_def);
        assert!(result.is_success());

        let module = result.module.unwrap();
        assert_eq!(module.protocol.fairness.len(), 2);
    }

    #[test]
    fn test_module_definition_builder() {
        let module = ModuleDefinition::new("test")
            .as_protocol()
            .with_protocol_name("TestProtocol");

        assert!(module.has_protocol_attr);
        assert_eq!(module.protocol_name, Some("TestProtocol".to_string()));
    }

    #[test]
    fn test_function_definition_builder() {
        let func = FunctionDefinition::new("test_action")
            .as_action()
            .with_action_name("do_something")
            .with_enabled(Predicate::Bool(true));

        assert!(func.is_action);
        assert_eq!(func.action_name, Some("do_something".to_string()));
        assert!(func.enabled.is_some());
    }

    #[test]
    fn test_stats_update() {
        let mut stats = ProtocolExtractorStats::new();

        let mut module = ProtocolModule::new("test");
        module.add_variable(StateVariable {
            name: "x".to_string(),
            ty: VcType::Int {
                signed: true,
                bits: 32,
            },
            type_invariant: None,
        });
        module.add_action(Action {
            name: "act".to_string(),
            enabled: Predicate::Bool(true),
            effect: vec![],
        });

        let result = ProtocolExtractionResult::success(module);
        stats.update_from_result(&result);

        assert_eq!(stats.modules_processed, 1);
        assert_eq!(stats.protocols_extracted, 1);
        assert_eq!(stats.total_variables, 1);
        assert_eq!(stats.total_actions, 1);
    }

    #[test]
    fn test_stats_with_errors() {
        let mut stats = ProtocolExtractorStats::new();

        let result = ProtocolExtractionResult::failure(vec![ProtocolExtractionError {
            kind: ProtocolExtractionErrorKind::MissingInit,
            message: "test error".to_string(),
            span: None,
        }]);
        stats.update_from_result(&result);

        assert_eq!(stats.modules_processed, 1);
        assert_eq!(stats.protocols_extracted, 0);
        assert_eq!(stats.total_errors, 1);
    }

    #[test]
    fn test_missing_init_with_strict_options() {
        let mut extractor = ProtocolExtractor::with_options(ProtocolExtractorOptions::strict());

        let module_def = ModuleDefinition::new("no_init").as_protocol();

        let result = extractor.extract(&module_def);
        assert!(!result.is_success());

        let has_missing_init_error = result
            .errors
            .iter()
            .any(|e| matches!(e.kind, ProtocolExtractionErrorKind::MissingInit));
        assert!(has_missing_init_error);
    }

    #[test]
    fn test_field_with_invariant() {
        // positive > 0
        let field = FieldDefinition::new(
            "positive",
            VcType::Int {
                signed: true,
                bits: 32,
            },
        )
        .with_invariant(Predicate::Expr(Expr::Gt(
            Box::new(Expr::Var("positive".to_string())),
            Box::new(Expr::IntLit(0)),
        )));

        assert!(field.type_invariant.is_some());
    }
}
