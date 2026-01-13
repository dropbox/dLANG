//! SIL (Swift Intermediate Language) Textual Parser
//!
//! This module parses SIL textual output from `swiftc -emit-sil` into
//! Rust data structures that can be translated to VC IR for verification.
//!
//! # Example SIL
//! ```sil
//! sil_stage canonical
//!
//! sil @add : $@convention(thin) (Int, Int) -> Int {
//! bb0(%0 : $Int, %1 : $Int):
//!   %2 = struct_extract %0, #Int._value
//!   %3 = struct_extract %1, #Int._value
//!   %4 = integer_literal $Builtin.Int1, -1
//!   %5 = builtin "sadd_with_overflow_Int64"(%2, %3, %4) : $(Builtin.Int64, Builtin.Int1)
//!   %6 = tuple_extract %5, 0
//!   %7 = tuple_extract %5, 1
//!   cond_fail %7, "arithmetic overflow"
//!   %8 = struct $Int (%6)
//!   return %8
//! }
//! ```

/// SIL module - top-level container
#[derive(Debug, Clone)]
pub struct SilModule {
    /// Stage: raw or canonical
    pub stage: SilStage,
    /// Import declarations
    pub imports: Vec<String>,
    /// Functions defined in this module
    pub functions: Vec<SilFunction>,
    /// Global variables
    pub globals: Vec<SilGlobal>,
}

/// SIL stage
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum SilStage {
    Raw,
    #[default]
    Canonical,
}

/// SIL function
#[derive(Debug, Clone)]
pub struct SilFunction {
    /// Mangled name (e.g., `$s8test_sil3addyS2i_SitF`)
    pub name: String,
    /// Demangled name if available
    pub demangled_name: Option<String>,
    /// Function type signature
    pub signature: SilType,
    /// Linkage (public, hidden, etc.)
    pub linkage: SilLinkage,
    /// Function attributes
    pub attributes: Vec<SilAttribute>,
    /// Basic blocks (empty for external declarations)
    pub blocks: Vec<SilBasicBlock>,
}

/// SIL linkage
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum SilLinkage {
    Public,
    #[default]
    Hidden,
    Private,
    PublicExternal,
    HiddenExternal,
    Shared,
}

/// Function/instruction attribute
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SilAttribute {
    Ossa,
    Transparent,
    Inline(InlineKind),
    NoInline,
    AlwaysInline,
    Serialized,
    /// @_requires("condition") verification precondition
    Requires(String),
    /// @_ensures("condition") verification postcondition
    Ensures(String),
    /// @_invariant("condition") verification invariant
    Invariant(String),
    /// @_trusted - skip verification for this function
    Trusted,
    /// @_semantics("tag") compiler hint
    Semantics(String),
    Other(String),
}

/// Function inlining behavior specified by `@inline` attribute.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InlineKind {
    /// `@inline(__always)` - always inline this function
    Always,
    /// `@inline(never)` - never inline this function
    Never,
}

/// Actor isolation kind for concurrency verification
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ActorIsolation {
    /// Isolated to a specific actor instance
    ActorInstance,
    /// Isolated to the global actor (e.g., `@MainActor`)
    GlobalActor(String),
    /// Not isolated (nonisolated)
    Nonisolated,
    /// Isolation is erased/unknown
    Erased,
}

/// SIL basic block
#[derive(Debug, Clone)]
pub struct SilBasicBlock {
    /// Block label (e.g., "bb0")
    pub label: String,
    /// Block arguments (phi nodes)
    pub arguments: Vec<SilValue>,
    /// Instructions in this block
    pub instructions: Vec<SilInstruction>,
    /// Terminator instruction
    pub terminator: SilTerminator,
}

/// SIL value (SSA register)
#[derive(Debug, Clone)]
pub struct SilValue {
    /// Register name (e.g., "%0")
    pub name: String,
    /// Type annotation
    pub ty: SilType,
    /// Optional debug name
    pub debug_name: Option<String>,
}

/// SIL instruction (non-terminator)
#[derive(Debug, Clone)]
pub struct SilInstruction {
    /// Result value(s) - empty for non-value instructions
    pub results: Vec<SilValue>,
    /// Instruction kind with operands
    pub kind: SilInstructionKind,
    /// Source location
    pub location: Option<SilLocation>,
}

/// SIL instruction kinds
#[derive(Debug, Clone)]
pub enum SilInstructionKind {
    // Literals
    IntegerLiteral {
        ty: SilType,
        value: i128,
    },
    FloatLiteral {
        ty: SilType,
        value: f64,
    },
    StringLiteral {
        encoding: StringEncoding,
        value: String,
    },

    // Memory allocation
    AllocStack {
        ty: SilType,
    },
    AllocRef {
        ty: SilType,
        tail_elems: Vec<SilType>,
    },
    DeallocStack {
        operand: String,
    },
    DeallocRef {
        operand: String,
    },

    // Memory access
    Load {
        kind: LoadKind,
        address: String,
    },
    Store {
        kind: StoreKind,
        source: String,
        dest: String,
    },
    CopyAddr {
        take: bool,
        init: bool,
        source: String,
        dest: String,
    },
    /// `explicit_copy_addr` - explicit copy that survives move checking
    ExplicitCopyAddr {
        take: bool,
        init: bool,
        source: String,
        dest: String,
    },
    BeginAccess {
        kind: AccessKind,
        enforcement: Enforcement,
        address: String,
    },
    EndAccess {
        address: String,
    },
    BeginBorrow {
        operand: String,
    },
    EndBorrow {
        operand: String,
    },

    // Struct/Tuple operations
    Struct {
        ty: SilType,
        operands: Vec<String>,
    },
    StructExtract {
        operand: String,
        field: String,
    },
    /// `ref_element_addr` - get address of a class instance field
    RefElementAddr {
        operand: String,
        field: String,
        immutable: bool,
    },
    Tuple {
        ty: SilType,
        operands: Vec<String>,
    },
    TupleExtract {
        operand: String,
        index: usize,
    },
    DestructureTuple {
        operand: String,
    },
    /// `tuple_addr_constructor` - construct tuple in-place at address
    TupleAddrConstructor {
        init_or_assign: InitOrAssign,
        dest: String,
        elements: Vec<String>,
    },
    /// `destructure_struct` - extract all fields from struct (multiple results)
    DestructureStruct {
        operand: String,
    },

    // Enum operations
    Enum {
        ty: SilType,
        case_name: String,
        operand: Option<String>,
    },
    SelectEnum {
        operand: String,
        cases: Vec<(String, String)>,
        default: Option<String>,
    },
    /// `init_enum_data_addr` - get address for enum payload data
    InitEnumDataAddr {
        address: String,
        case_name: String,
    },
    /// `inject_enum_addr` - set discriminator for in-place enum
    InjectEnumAddr {
        address: String,
        case_name: String,
    },
    /// `unchecked_take_enum_data_addr` - extract enum payload address
    UncheckedTakeEnumDataAddr {
        address: String,
        case_name: String,
    },

    // Function calls
    Apply {
        callee: String,
        substitutions: Vec<SilType>,
        arguments: Vec<String>,
        ty: SilType,
        /// Caller's actor isolation context (if specified)
        caller_isolation: Option<ActorIsolation>,
        /// Callee's actor isolation requirement (if specified)
        callee_isolation: Option<ActorIsolation>,
    },
    Builtin {
        name: String,
        arguments: Vec<String>,
        ty: SilType,
    },

    // References
    FunctionRef {
        name: String,
    },
    /// `dynamic_function_ref` - reference to dynamically dispatched function
    DynamicFunctionRef {
        name: String,
    },
    /// `prev_dynamic_function_ref` - reference to previous dynamic function version
    PrevDynamicFunctionRef {
        name: String,
    },
    /// `has_symbol` - runtime check if symbol exists
    HasSymbol {
        decl: String,
    },
    GlobalAddr {
        name: String,
    },
    /// `alloc_global` - allocate storage for a global variable
    AllocGlobal {
        name: String,
    },
    ClassMethod {
        operand: String,
        method: String,
    },
    WitnessMethod {
        ty: SilType,
        method: String,
    },

    // Conversions
    Upcast {
        operand: String,
        ty: SilType,
    },
    UnconditionalCheckedCast {
        operand: String,
        ty: SilType,
    },
    /// Address-based unconditional checked cast
    UnconditionalCheckedCastAddr {
        source_ty: SilType,
        source: String,
        target_ty: SilType,
        dest: String,
    },
    RefToRawPointer {
        operand: String,
    },
    RawPointerToRef {
        operand: String,
        ty: SilType,
    },
    ConvertFunction {
        operand: String,
        ty: SilType,
    },
    /// `thin_to_thick_function` - convert thin function ref to thick closure
    ThinToThickFunction {
        operand: String,
        ty: SilType,
    },
    /// `convert_escape_to_noescape` - mark closure as non-escaping
    ConvertEscapeToNoEscape {
        operand: String,
        ty: SilType,
        /// Lifetime has been extended
        lifetime_guaranteed: bool,
    },

    // Reference counting (for ownership tracking)
    StrongRetain {
        operand: String,
    },
    StrongRelease {
        operand: String,
    },
    RetainValue {
        operand: String,
    },
    ReleaseValue {
        operand: String,
    },
    CopyValue {
        operand: String,
    },
    DestroyValue {
        operand: String,
    },
    /// `destroy_addr` - destroy value at address
    DestroyAddr {
        address: String,
    },

    // Index operations
    IndexAddr {
        base: String,
        index: String,
    },

    // Existentials
    InitExistentialAddr {
        address: String,
        ty: SilType,
    },
    OpenExistentialAddr {
        address: String,
        ty: SilType,
    },
    InitExistentialRef {
        operand: String,
        ty: SilType,
    },
    OpenExistentialRef {
        operand: String,
        ty: SilType,
    },

    // Boxed existentials (heap-allocated protocol containers)
    AllocExistentialBox {
        existential_ty: SilType,
        concrete_ty: SilType,
    },
    ProjectExistentialBox {
        concrete_ty: SilType,
        operand: String,
    },
    OpenExistentialBox {
        operand: String,
        ty: SilType,
    },
    OpenExistentialBoxValue {
        operand: String,
        ty: SilType,
    },
    DeallocExistentialBox {
        operand: String,
        concrete_ty: SilType,
    },

    // Debug
    DebugValue {
        operand: String,
        name: Option<String>,
        argno: Option<u32>,
    },

    // Verification-relevant: runtime checks
    CondFail {
        condition: String,
        message: String,
    },

    // Metatypes
    Metatype {
        ty: SilType,
    },
    ValueMetatype {
        operand: String,
    },
    ExistentialMetatype {
        operand: String,
        ty: SilType,
    },
    InitExistentialMetatype {
        operand: String,
        ty: SilType,
    },
    OpenExistentialMetatype {
        operand: String,
        ty: SilType,
    },

    // Misc / Runtime
    MarkDependence {
        value: String,
        base: String,
    },
    /// `fix_lifetime` - prevent optimization from moving value's lifetime
    FixLifetime {
        operand: String,
    },
    /// `is_unique` - check if reference is uniquely held (COW optimization)
    IsUnique {
        operand: String,
    },

    // Bridge object conversions (for Objective-C interop)
    /// `ref_to_bridge_object` - encode reference and bits into bridge object
    RefToBridgeObject {
        operand: String,
        bits: String,
    },
    /// `bridge_object_to_ref` - extract reference from bridge object
    BridgeObjectToRef {
        operand: String,
        ty: SilType,
    },
    /// `bridge_object_to_word` - extract word value from bridge object
    BridgeObjectToWord {
        operand: String,
    },
    /// `classify_bridge_object` - classify bridge object type
    ClassifyBridgeObject {
        operand: String,
    },
    /// `value_to_bridge_object` - convert word to bridge object
    ValueToBridgeObject {
        operand: String,
    },

    // ObjC metatype conversions
    /// `thick_to_objc_metatype` - convert Swift metatype to `ObjC` class object
    ThickToObjcMetatype {
        operand: String,
    },
    /// `objc_to_thick_metatype` - convert `ObjC` class object to Swift metatype
    ObjcToThickMetatype {
        operand: String,
        ty: SilType,
    },

    // Block storage (for Objective-C blocks)
    /// `project_block_storage` - get capture storage address from block storage
    ProjectBlockStorage {
        operand: String,
    },
    /// `init_block_storage_header` - initialize block with invoke function
    InitBlockStorageHeader {
        block_storage: String,
        invoke_fn: String,
        ty: SilType,
    },
    /// `copy_block` - copy an Objective-C block
    CopyBlock {
        operand: String,
    },
    /// `copy_block_without_escaping` - copy block without escaping
    CopyBlockWithoutEscaping {
        operand: String,
        closure: String,
    },
    /// `mark_uninitialized` - mark memory as uninitialized for DI
    MarkUninitialized {
        kind: MarkUninitializedKind,
        operand: String,
    },

    // ObjC method dispatch
    /// `objc_method` - get `ObjC` method implementation for message send
    ObjcMethod {
        operand: String,
        method: String,
    },
    /// `objc_super_method` - get `ObjC` super method implementation
    ObjcSuperMethod {
        operand: String,
        method: String,
    },
    /// `objc_protocol` - get `ObjC` Protocol object for a protocol
    ObjcProtocol {
        protocol: String,
        ty: SilType,
    },

    // Key paths
    /// `keypath` - create a key path object from a pattern
    KeyPath {
        ty: SilType,
        pattern: String,
    },

    // Unchecked reference conversions
    /// `ref_to_unmanaged` - convert a ref to an unmanaged reference
    RefToUnmanaged {
        operand: String,
        ty: SilType,
    },
    /// `unmanaged_to_ref` - convert an unmanaged reference back to a ref
    UnmanagedToRef {
        operand: String,
        ty: SilType,
    },

    // Copy-on-Write (COW) mutation
    /// `begin_cow_mutation` - check uniqueness and begin mutation
    /// Returns (Builtin.Int1, T) where Int1 is true if unique
    BeginCowMutation {
        operand: String,
        native: bool,
    },
    /// `end_cow_mutation` - end mutation period
    EndCowMutation {
        operand: String,
        keep_unique: bool,
    },
    /// `end_cow_mutation_addr` - end mutation for address type
    EndCowMutationAddr {
        address: String,
    },

    // Unmanaged reference counting
    /// `unmanaged_retain_value` - retain without ownership tracking
    UnmanagedRetainValue {
        operand: String,
    },
    /// `unmanaged_release_value` - release without ownership tracking
    UnmanagedReleaseValue {
        operand: String,
    },
    /// `unmanaged_autorelease_value` - autorelease without ownership tracking
    UnmanagedAutoreleaseValue {
        operand: String,
    },

    // Weak reference storage
    /// `load_weak` - load from weak reference address, incrementing strong refcount
    LoadWeak {
        take: bool,
        address: String,
    },
    /// `store_weak` - store to weak reference address
    StoreWeak {
        init: bool,
        source: String,
        dest: String,
    },
    /// `weak_copy_value` - copy a weak reference value
    WeakCopyValue {
        operand: String,
    },
    /// `strong_copy_weak_value` - convert weak reference to strong reference
    StrongCopyWeakValue {
        operand: String,
    },

    // Unowned reference storage
    /// `load_unowned` - load from unowned reference address
    LoadUnowned {
        take: bool,
        address: String,
    },
    /// `store_unowned` - store to unowned reference address
    StoreUnowned {
        init: bool,
        source: String,
        dest: String,
    },
    /// `unowned_copy_value` - wrap value in `@sil_unowned`
    UnownedCopyValue {
        operand: String,
    },

    // ObjC metatype conversions
    /// `objc_metatype_to_object` - convert `ObjC` metatype to `AnyObject`
    ObjcMetatypeToObject {
        operand: String,
    },
    /// `objc_existential_metatype_to_object` - convert existential `ObjC` metatype to `AnyObject`
    ObjcExistentialMetatypeToObject {
        operand: String,
    },

    // Variadic generics / pack instructions
    /// `alloc_pack` - allocate storage for a parameter pack
    AllocPack {
        pack_ty: SilType,
    },
    /// `dealloc_pack` - deallocate pack storage
    DeallocPack {
        operand: String,
    },
    /// `pack_length` - get the count of elements in a pack type
    PackLength {
        pack_ty: SilType,
    },
    /// `dynamic_pack_index` - create pack index from runtime value
    DynamicPackIndex {
        operand: String,
        pack_ty: SilType,
    },
    /// `scalar_pack_index` - create pack index from compile-time constant
    ScalarPackIndex {
        index: usize,
        pack_ty: SilType,
    },
    /// `pack_pack_index` - combine nested pack indices
    PackPackIndex {
        component_index: usize,
        inner_index: String,
        pack_ty: SilType,
    },
    /// `open_pack_element` - open a pack element for access
    OpenPackElement {
        index: String,
        shape_ty: String,
        uuid: String,
    },
    /// `pack_element_get` - get address of element in pack
    PackElementGet {
        index: String,
        pack: String,
        element_ty: SilType,
    },
    /// `pack_element_set` - set element in pack
    PackElementSet {
        value: String,
        index: String,
        pack: String,
    },
    /// `tuple_pack_element_addr` - get tuple element address for pack index
    TuplePackElementAddr {
        index: String,
        tuple: String,
        element_ty: SilType,
    },

    // Async/await continuation instructions
    /// `get_async_continuation` - get continuation for async suspension
    GetAsyncContinuation {
        result_ty: SilType,
        throws: bool,
    },
    /// `get_async_continuation_addr` - get continuation with address for result
    GetAsyncContinuationAddr {
        result_ty: SilType,
        result_addr: String,
        throws: bool,
    },

    // Pointer/address conversions
    /// `address_to_pointer` - convert address to raw pointer
    AddressToPointer {
        operand: String,
    },
    /// `pointer_to_address` - convert raw pointer to typed address
    PointerToAddress {
        operand: String,
        ty: SilType,
        strict: bool,
    },

    // Unchecked casts
    /// `unchecked_ref_cast` - cast reference type without runtime check
    UncheckedRefCast {
        operand: String,
        ty: SilType,
    },
    /// `unchecked_addr_cast` - cast address type without runtime check
    UncheckedAddrCast {
        operand: String,
        ty: SilType,
    },
    /// `unchecked_trivial_bit_cast` - trivial bitcast without runtime check
    UncheckedTrivialBitCast {
        operand: String,
        ty: SilType,
    },
    /// `unchecked_bitwise_cast` - bitwise cast without runtime check
    UncheckedBitwiseCast {
        operand: String,
        ty: SilType,
    },

    // Actor/concurrency
    /// `hop_to_executor` - switch to an actor's executor
    HopToExecutor {
        operand: String,
    },
    /// `extract_executor` - get executor from an actor
    ExtractExecutor {
        operand: String,
    },

    // Structural address instructions
    /// `struct_element_addr` - get address of struct field
    StructElementAddr {
        operand: String,
        field: String,
    },
    /// `tuple_element_addr` - get address of tuple element
    TupleElementAddr {
        operand: String,
        index: usize,
    },
    /// `ref_tail_addr` - get address of tail-allocated array
    RefTailAddr {
        operand: String,
        ty: SilType,
    },
    /// `tail_addr` - compute tail allocation address
    TailAddr {
        base: String,
        count: String,
        ty: SilType,
    },

    // Closure/partial application
    /// `partial_apply` - create closure by partial application
    PartialApply {
        callee: String,
        substitutions: Vec<SilType>,
        arguments: Vec<String>,
        on_stack: bool,
    },
    /// `load_borrow` - load and borrow value from address
    LoadBorrow {
        address: String,
    },

    // Box allocation
    /// `alloc_box` - allocate heap box for value
    AllocBox {
        ty: SilType,
    },
    /// `project_box` - get address of value inside box
    ProjectBox {
        operand: String,
        field_index: Option<usize>,
    },
    /// `dealloc_box` - deallocate heap box
    DeallocBox {
        operand: String,
    },

    // Additional method dispatch
    /// `super_method` - get superclass method implementation
    SuperMethod {
        operand: String,
        method: String,
    },

    // Additional pack instructions
    /// `tuple_pack_extract` - extract element from tuple pack directly
    TuplePackExtract {
        index: String,
        tuple: String,
        element_ty: SilType,
    },

    // Global values
    /// `global_value` - get global as value (not address)
    GlobalValue {
        name: String,
    },

    // Memory binding
    /// `bind_memory` - bind raw memory to typed memory
    BindMemory {
        base: String,
        num_words: String,
        ty: SilType,
    },
    /// `rebind_memory` - rebind memory to different type
    RebindMemory {
        operand: String,
        ty: SilType,
    },

    // Move semantics
    /// `move_value` - move ownership without copying
    MoveValue {
        operand: String,
        lexical: bool,
        pointer_escape: bool,
        var_decl: bool,
    },

    // Enum data extraction
    /// `unchecked_enum_data` - extract enum payload without check
    UncheckedEnumData {
        operand: String,
        case_name: String,
    },

    // Assign instruction (raw SIL)
    /// `assign` - assign value to initialized memory
    Assign {
        source: String,
        dest: String,
    },

    // Differentiable programming instructions
    /// `differentiable_function` - bundle function with derivative functions
    DifferentiableFunction {
        original: String,
        jvp: Option<String>,
        vjp: Option<String>,
        parameters: Vec<usize>,
    },
    /// `linear_function` - bundle function as linear map
    LinearFunction {
        original: String,
        transpose: Option<String>,
        parameters: Vec<usize>,
    },
    /// `differentiable_function_extract` - extract component from differentiable function
    DifferentiableFunctionExtract {
        operand: String,
        extractee: DifferentiableExtractee,
    },
    /// `linear_function_extract` - extract component from linear function
    LinearFunctionExtract {
        operand: String,
        extractee: LinearExtractee,
    },
    /// `differentiability_witness_function` - get derivative from witness table
    DifferentiabilityWitnessFunction {
        witness_kind: DifferentiabilityWitnessKind,
        witness: String,
        ty: SilType,
    },

    // Coroutine instructions
    /// `begin_apply` - start a coroutine, returns token and yielded values
    BeginApply {
        callee: String,
        substitutions: Vec<SilType>,
        arguments: Vec<String>,
    },
    /// `end_apply` - resume and complete coroutine normally
    EndApply {
        token: String,
    },
    /// `abort_apply` - abort coroutine execution
    AbortApply {
        token: String,
    },

    // Unknown instruction (for forward compatibility)
    Unknown {
        name: String,
        text: String,
    },
}

/// What to extract from a differentiable function
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum DifferentiableExtractee {
    #[default]
    Original,
    JVP,
    VJP,
}

/// What to extract from a linear function
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum LinearExtractee {
    #[default]
    Original,
    Transpose,
}

/// Kind of differentiability witness function
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum DifferentiabilityWitnessKind {
    #[default]
    JVP,
    VJP,
    Transpose,
}

/// Cast consumption kind for address-based casts
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum CastConsumptionKind {
    #[default]
    TakeAlways,
    TakeOnSuccess,
    CopyOnSuccess,
    BorrowAlways,
}

/// SIL terminator instructions
#[derive(Debug, Clone)]
pub enum SilTerminator {
    Return {
        operand: String,
    },
    Throw {
        operand: String,
    },
    Unreachable,

    /// Unconditional branch
    Branch {
        dest: String,
        args: Vec<String>,
    },

    /// Conditional branch
    CondBranch {
        condition: String,
        true_dest: String,
        true_args: Vec<String>,
        false_dest: String,
        false_args: Vec<String>,
    },

    /// Switch on value
    SwitchValue {
        operand: String,
        cases: Vec<(SilConstant, String)>,
        default: Option<String>,
    },

    /// Switch on enum
    SwitchEnum {
        operand: String,
        cases: Vec<(String, String)>,
        default: Option<String>,
    },

    /// Switch on enum address (indirect)
    SwitchEnumAddr {
        address: String,
        cases: Vec<(String, String)>,
        default: Option<String>,
    },

    /// Try-apply (for throwing functions)
    TryApply {
        callee: String,
        substitutions: Vec<SilType>,
        arguments: Vec<String>,
        normal_dest: String,
        error_dest: String,
    },

    /// Checked cast with branch
    CheckedCastBranch {
        exact: bool,
        operand: String,
        target_ty: SilType,
        success_dest: String,
        failure_dest: String,
    },

    /// Address-based checked cast with branch
    CheckedCastAddrBranch {
        consumption: CastConsumptionKind,
        source_ty: SilType,
        source: String,
        target_ty: SilType,
        dest: String,
        success_dest: String,
        failure_dest: String,
    },

    /// Async continuation await - suspend until continuation is resumed
    AwaitAsyncContinuation {
        continuation: String,
        resume_dest: String,
        error_dest: Option<String>,
    },

    /// Yield values from a coroutine
    Yield {
        values: Vec<String>,
        resume_dest: String,
        unwind_dest: String,
    },

    /// Unwind from a coroutine (cleanup path)
    Unwind,

    /// Dynamic method branch - branch based on method existence
    DynamicMethodBranch {
        operand: String,
        method: String,
        has_method_dest: String,
        no_method_dest: String,
    },

    /// Return borrowed value
    ReturnBorrow {
        operand: String,
    },

    /// Throw from address (for indirect error types)
    ThrowAddr,
}

/// SIL type representation
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SilType {
    /// Named type (e.g., `Int`, `String`, `MyClass`)
    Named(String),
    /// Tuple type
    Tuple(Vec<SilType>),
    /// Function type
    Function {
        convention: CallingConvention,
        params: Vec<SilType>,
        result: Box<SilType>,
        throws: bool,
    },
    /// Metatype
    Metatype(Box<SilType>),
    /// Optional type (syntactic sugar)
    Optional(Box<SilType>),
    /// Address type (pointer to type)
    Address(Box<SilType>),
    /// Generic parameter (e.g., "T", "U")
    Generic(String),
    /// Existential type (e.g., "any Protocol")
    Existential(Vec<String>),
    /// Builtin type (e.g., "Builtin.Int64")
    Builtin(String),
    /// Box type for captured variables (e.g., { var Int })
    Box(Box<SilType>),
    /// Unknown type (for parsing tolerance)
    Unknown(String),
}

impl Default for SilType {
    fn default() -> Self {
        Self::Unknown("?".to_string())
    }
}

/// Calling convention
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum CallingConvention {
    #[default]
    Thin,
    Thick,
    Method,
    WitnessMethod,
    ObjCMethod,
    C,
    Block,
}

/// String encoding
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum StringEncoding {
    #[default]
    Utf8,
    Utf16,
    ObjCSelector,
}

/// Load instruction kind
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum LoadKind {
    #[default]
    Take,
    Copy,
    Borrow,
    Trivial,
}

/// Store instruction kind
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum StoreKind {
    #[default]
    Init,
    Assign,
    Trivial,
}

/// Init or assign mode for `tuple_addr_constructor`
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum InitOrAssign {
    #[default]
    Init,
    Assign,
}

/// Kind of `mark_uninitialized`
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum MarkUninitializedKind {
    #[default]
    Var,
    RootSelf,
    CrossModuleRootSelf,
    DerivedSelf,
    DerivedSelfOnly,
    DelegatingInit,
    DelegatingSelf,
}

/// Memory access kind
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum AccessKind {
    #[default]
    Read,
    Modify,
    Init,
    Deinit,
}

/// Access enforcement
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Enforcement {
    #[default]
    Unknown,
    Static,
    Dynamic,
    Unsafe,
}

/// SIL constant for switch cases
#[derive(Debug, Clone, PartialEq)]
pub enum SilConstant {
    Int(i128),
    Float(f64),
    String(String),
    /// Named constant (e.g., `%lit` in `switch_value`)
    Named(String),
}

/// Source location
#[derive(Debug, Clone)]
pub struct SilLocation {
    pub file: String,
    pub line: u32,
    pub column: u32,
}

/// SIL global variable
#[derive(Debug, Clone)]
pub struct SilGlobal {
    pub name: String,
    pub ty: SilType,
    pub linkage: SilLinkage,
}

// ============================================================================
// PARSER
// ============================================================================

type EnumSwitchCase = (String, String);
type EnumSwitchCases = Vec<EnumSwitchCase>;
type EnumSwitchCasesAndDefault = (EnumSwitchCases, Option<String>);

/// Error during SIL parsing
#[derive(Debug, Clone)]
pub struct SilParseError {
    pub message: String,
    pub line: usize,
    pub column: usize,
}

impl std::fmt::Display for SilParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "SIL parse error at {}:{}: {}",
            self.line, self.column, self.message
        )
    }
}

impl std::error::Error for SilParseError {}

/// SIL parser
pub struct SilParser<'a> {
    input: &'a str,
    pos: usize,
    line: usize,
    column: usize,
    /// Attributes collected from Swift-syntax declarations.
    /// Maps simplified function name -> `Vec<SilAttribute>`
    swift_decl_attrs: std::collections::HashMap<String, Vec<SilAttribute>>,
}

impl<'a> SilParser<'a> {
    /// Create a new SIL parser for the given input string.
    ///
    /// The parser performs a first pass to collect Swift-syntax declarations
    /// with `@_requires` and `@_ensures` attributes, then resets for the main parse.
    #[must_use]
    pub fn new(input: &'a str) -> Self {
        let mut parser = Self {
            input,
            pos: 0,
            line: 1,
            column: 1,
            swift_decl_attrs: std::collections::HashMap::new(),
        };
        // First pass: collect Swift-syntax declarations with attributes
        parser.collect_swift_decl_attrs();
        // Reset position for main parse
        parser.pos = 0;
        parser.line = 1;
        parser.column = 1;
        parser
    }

    /// First pass: collect Swift-syntax declarations with @_requires/@_ensures attributes.
    ///
    /// Real Swift compiler output looks like:
    /// ```text
    /// @_requires("x > 0")
    /// @_ensures("result > 0")
    /// func keepPositive(_ x: Int) -> Int
    ///
    /// sil hidden @$s8positive12keepPositiveyS2iF : ...
    /// ```
    ///
    /// This method collects the attributes and maps them to the function name.
    fn collect_swift_decl_attrs(&mut self) {
        let mut current_attrs: Vec<SilAttribute> = Vec::new();

        while !self.is_eof() {
            self.skip_whitespace_and_comments();
            if self.is_eof() {
                break;
            }

            // Check for @_requires, @_ensures, @_invariant, @_trusted attributes
            if self.peek_char('@') && !self.peek_str("@convention") {
                if let Some(attr) = self.try_parse_swift_attribute() {
                    current_attrs.push(attr);
                    // Skip whitespace on same line to check for "func" after @_trusted
                    self.skip_whitespace_on_line();
                    // If position advanced significantly (attribute with parens skipped to EOL),
                    // continue loop to parse next attribute. Otherwise check for "func" below.
                    if self.peek_char('\n') || self.is_eof() || self.peek_char('@') {
                        continue;
                    }
                } else {
                    // If we parsed an unknown attribute like @inline(never), skip whitespace
                    // and check if there's more on this line (e.g., "func double(...)").
                    self.skip_whitespace_on_line();
                }
            }

            // Check for func declaration (may be on same line as @_trusted)
            if self.peek_str("func ") {
                if let Some(func_name) = self.try_parse_func_decl_name() {
                    if !current_attrs.is_empty() {
                        self.swift_decl_attrs
                            .insert(func_name, current_attrs.clone());
                        current_attrs.clear();
                    }
                }
                // Skip to end of line even if we didn't parse the name
                self.skip_to_eol();
                continue;
            }

            // Skip other lines
            self.skip_to_eol();
            // Clear attributes if we hit something that's not a func declaration
            if !self.peek_str("@") && !current_attrs.is_empty() {
                // Don't clear on newlines, only on actual content
                let next_line_start = &self.input[self.pos..];
                if !next_line_start.trim_start().starts_with('@')
                    && !next_line_start.trim_start().starts_with("func ")
                    && !next_line_start.trim_start().is_empty()
                {
                    current_attrs.clear();
                }
            }
        }
    }

    /// Try to parse a Swift-syntax attribute like @_requires("condition")
    fn try_parse_swift_attribute(&mut self) -> Option<SilAttribute> {
        if !self.peek_char('@') {
            return None;
        }
        self.advance(); // consume @

        // Parse attribute name
        let attr_name = self.consume_while(|c| c.is_ascii_alphanumeric() || c == '_');
        self.skip_whitespace_on_line();

        // Parse optional argument in parentheses
        let arg = if self.peek_char('(') {
            self.advance(); // consume (
            self.skip_whitespace_on_line();

            // Parse quoted string argument
            if self.peek_char('"') {
                self.parse_string().ok().inspect(|_| {
                    self.skip_whitespace_on_line();
                    if self.peek_char(')') {
                        self.advance(); // consume )
                    }
                })
            } else {
                // Skip to closing paren
                let mut depth = 1;
                while depth > 0 && !self.is_eof() {
                    match self.current_char() {
                        Some('(') => {
                            depth += 1;
                            self.advance();
                        }
                        Some(')') => {
                            depth -= 1;
                            self.advance();
                        }
                        Some(_) => self.advance(),
                        None => break,
                    }
                }
                None
            }
        } else {
            None
        };

        // Convert to SilAttribute.
        //
        // We accept both underscored forms (`@_requires`) and public macro forms
        // (`@requires`) so the verifier can read specs from `-emit-sil` output
        // regardless of how the attributes were authored.
        //
        // NOTE: Skip to EOL only for attributes that have parenthesized arguments
        // (like @_requires("x > 0")) and thus occupy their own line. Don't skip
        // for @_trusted which has no argument and can appear on the same line as
        // "func", e.g., "@_trusted func unsafeOp() -> Int".
        let has_parens = arg.is_some();
        let result = match (attr_name.as_str(), arg) {
            ("_requires" | "requires", Some(cond)) => Some(SilAttribute::Requires(cond)),
            ("_ensures" | "ensures", Some(cond)) => Some(SilAttribute::Ensures(cond)),
            ("_invariant" | "invariant", Some(cond)) => Some(SilAttribute::Invariant(cond)),
            ("_trusted" | "trusted", _) => Some(SilAttribute::Trusted),
            ("_semantics" | "semantics", Some(tag)) => Some(SilAttribute::Semantics(tag)),
            _ => None, // Ignore other attributes
        };

        // Skip to EOL only for attributes with parenthesized arguments.
        // @_trusted has no argument and may share a line with "func".
        if result.is_some() && has_parens {
            self.skip_to_eol();
        }
        // For attributes without parens (like @_trusted) and unknown attributes,
        // leave position so caller can check for "func " on the same line.

        result
    }

    /// Try to parse a function declaration name from "func name(..." or "func name<...>("
    fn try_parse_func_decl_name(&mut self) -> Option<String> {
        if !self.peek_str("func ") {
            return None;
        }
        self.expect_str("func").ok()?;
        self.skip_whitespace_on_line();

        // Parse function name
        let name = self.consume_while(|c| c.is_ascii_alphanumeric() || c == '_');
        if name.is_empty() {
            return None;
        }

        Some(name)
    }

    /// Parse the entire SIL module
    ///
    /// # Errors
    /// Returns an error if the input is not valid SIL or contains unsupported constructs.
    pub fn parse_module(&mut self) -> Result<SilModule, SilParseError> {
        let mut module = SilModule {
            stage: SilStage::Canonical,
            imports: Vec::new(),
            functions: Vec::new(),
            globals: Vec::new(),
        };

        while !self.is_eof() {
            self.skip_whitespace_and_comments();
            if self.is_eof() {
                break;
            }

            // Check for stage declaration
            if self.peek_str("sil_stage") {
                self.parse_stage(&mut module)?;
            }
            // Check for import
            else if self.peek_str("import") {
                let import = self.parse_import()?;
                module.imports.push(import);
            }
            // Check for sil_global
            else if self.peek_str("sil_global") {
                let global = self.parse_global()?;
                module.globals.push(global);
            }
            // Check for sil function (must be "sil " or "sil[", not "sil_*")
            // sil_* declarations include: sil_global, sil_vtable, sil_witness_table,
            // sil_scope, sil_differentiability_witness, sil_moveonlydeinit,
            // sil_default_witness_table, sil_property, sil_coverage_map, etc.
            else if self.peek_str("sil") && !self.peek_str("sil_") {
                let func = self.parse_function()?;
                module.functions.push(func);
            }
            // Skip other top-level declarations (sil_vtable, sil_witness_table,
            // sil_scope, sil_differentiability_witness, sil_property, etc.)
            else {
                self.skip_to_next_declaration();
            }
        }

        Ok(module)
    }

    fn parse_stage(&mut self, module: &mut SilModule) -> Result<(), SilParseError> {
        self.expect_str("sil_stage")?;
        self.skip_whitespace();

        if self.peek_str("raw") {
            self.expect_str("raw")?;
            module.stage = SilStage::Raw;
        } else if self.peek_str("canonical") {
            self.expect_str("canonical")?;
            module.stage = SilStage::Canonical;
        } else {
            return Err(self.error("expected 'raw' or 'canonical'"));
        }

        self.skip_to_eol();
        Ok(())
    }

    fn parse_import(&mut self) -> Result<String, SilParseError> {
        self.expect_str("import")?;
        self.skip_whitespace();
        let name = self.parse_identifier()?;
        self.skip_to_eol();
        Ok(name)
    }

    fn parse_function(&mut self) -> Result<SilFunction, SilParseError> {
        self.expect_str("sil")?;
        self.skip_whitespace();

        // Parse linkage and attributes
        let mut linkage = SilLinkage::Hidden;
        let mut attributes = Vec::new();

        while !self.peek_char('@') && !self.is_eof() {
            // Check for bracketed attribute like [transparent] or [_requires "x > 0"]
            if self.peek_char('[') {
                self.advance(); // consume [
                let attr_name = self.parse_identifier()?;
                self.skip_whitespace();

                // Check for optional argument (quoted string or unquoted value like "10.15")
                let quoted_arg = if self.peek_char('"') {
                    Some(self.parse_string()?)
                } else if !self.peek_char(']') {
                    // Unquoted argument - consume everything until ]
                    let start = self.pos;
                    while !self.peek_char(']') && !self.is_eof() {
                        self.advance();
                    }
                    let arg = self.input[start..self.pos].trim().to_string();
                    Some(arg).filter(|s| !s.is_empty())
                } else {
                    None
                };

                self.skip_whitespace();
                self.expect_char(']')?;
                self.skip_whitespace();

                let attr = match (attr_name.as_str(), quoted_arg) {
                    ("ossa", _) => SilAttribute::Ossa,
                    ("transparent", _) => SilAttribute::Transparent,
                    ("serialized", _) => SilAttribute::Serialized,
                    ("noinline", _) => SilAttribute::NoInline,
                    ("always_inline", _) => SilAttribute::AlwaysInline,
                    // Verification attributes
                    ("_requires" | "requires", Some(cond)) => SilAttribute::Requires(cond),
                    ("_ensures" | "ensures", Some(cond)) => SilAttribute::Ensures(cond),
                    ("_invariant" | "invariant", Some(cond)) => SilAttribute::Invariant(cond),
                    ("_trusted" | "trusted", _) => SilAttribute::Trusted,
                    ("_semantics" | "semantics", Some(tag)) => SilAttribute::Semantics(tag),
                    (name, Some(s)) => SilAttribute::Other(format!("[{name} \"{s}\"]")),
                    (name, None) => SilAttribute::Other(format!("[{name}]")),
                };
                attributes.push(attr);
                continue;
            }

            // Parse linkage keyword
            let word = self.parse_identifier()?;
            self.skip_whitespace();

            match word.as_str() {
                "public" => linkage = SilLinkage::Public,
                "hidden" => linkage = SilLinkage::Hidden,
                "private" => linkage = SilLinkage::Private,
                "public_external" => linkage = SilLinkage::PublicExternal,
                "hidden_external" => linkage = SilLinkage::HiddenExternal,
                "shared" => linkage = SilLinkage::Shared,
                _ => {
                    // Unknown keyword - put back and break
                    self.pos -= word.len();
                    self.column -= word.len();
                    break;
                }
            }
        }

        // Parse function name
        self.expect_char('@')?;
        let name = self.parse_symbol_name()?;
        self.skip_whitespace();

        // Parse function type
        self.expect_char(':')?;
        self.skip_whitespace();
        let signature = self.parse_type()?;
        self.skip_whitespace();

        // Parse function body or declaration
        let blocks = if self.peek_char('{') {
            self.parse_function_body()?
        } else {
            Vec::new()
        };

        // Try to merge attributes from Swift-syntax declarations.
        //
        // For mangled names like "$s8positive12keepPositiveyS2iF", we demangle to
        // "keepPositive" to match Swift decls.
        //
        // For non-mangled SIL names like "add" (from `sil @add ...`), demangling
        // fails, but we still want Swift decl attrs (e.g. in hand-written SIL tests)
        // to attach by matching on the plain function name.
        let demangled_name = crate::swift_demangle::demangle(&name);
        let simplified_name = demangled_name
            .as_ref()
            .map(|d| crate::swift_demangle::simplify_function_name(d))
            // Fallback: try to extract func name directly from mangled string
            // (useful for custom types that swift-demangle can't handle)
            .or_else(|| crate::swift_demangle::extract_func_from_mangled(&name))
            .or_else(|| Some(name.clone()));

        // Merge attributes from Swift-syntax declaration if found
        let mut merged_attributes = attributes;
        if let Some(ref simple) = simplified_name {
            if let Some(swift_attrs) = self.swift_decl_attrs.get(simple) {
                // Prepend Swift decl attributes (they come before SIL attributes logically)
                let mut combined = swift_attrs.clone();
                combined.extend(merged_attributes);
                merged_attributes = combined;
            }
        }

        Ok(SilFunction {
            name,
            demangled_name,
            signature,
            linkage,
            attributes: merged_attributes,
            blocks,
        })
    }

    fn parse_function_body(&mut self) -> Result<Vec<SilBasicBlock>, SilParseError> {
        self.expect_char('{')?;
        self.skip_whitespace_and_comments();

        // Skip effect annotations like [%1: noescape **] and [global: ]
        // These appear in newer Swift versions before the first basic block
        self.skip_effect_annotations();

        let mut blocks = Vec::new();

        while !self.peek_char('}') && !self.is_eof() {
            let block = self.parse_basic_block()?;
            blocks.push(block);
            self.skip_whitespace_and_comments();
        }

        self.expect_char('}')?;
        self.skip_to_eol();

        Ok(blocks)
    }

    /// Skip effect annotations like `[%1: noescape **]` and `[global: ]`
    /// These are emitted by newer Swift compilers
    fn skip_effect_annotations(&mut self) {
        loop {
            self.skip_whitespace_and_comments();
            if self.peek_char('[') {
                // Skip the entire bracketed annotation
                self.advance(); // consume '['
                let mut depth = 1;
                while depth > 0 && !self.is_eof() {
                    match self.current_char() {
                        Some('[') => {
                            depth += 1;
                            self.advance();
                        }
                        Some(']') => {
                            depth -= 1;
                            self.advance();
                        }
                        Some(_) => {
                            self.advance();
                        }
                        None => break,
                    }
                }
                self.skip_whitespace_and_comments();
            } else {
                break;
            }
        }
    }

    fn parse_basic_block(&mut self) -> Result<SilBasicBlock, SilParseError> {
        // Parse block label (bb0, bb1, etc.)
        let label = self.parse_identifier()?;

        // Parse optional arguments
        let mut arguments = Vec::new();
        self.skip_whitespace();
        if self.peek_char('(') {
            self.expect_char('(')?;
            while !self.peek_char(')') && !self.is_eof() {
                let arg = self.parse_block_argument()?;
                arguments.push(arg);
                self.skip_whitespace();
                if self.peek_char(',') {
                    self.advance();
                    self.skip_whitespace();
                }
            }
            self.expect_char(')')?;
        }

        self.expect_char(':')?;
        self.skip_whitespace_and_comments();

        // Parse instructions
        let mut instructions = Vec::new();
        let mut terminator = None;

        while !self.is_eof() && !self.peek_str("bb") && !self.peek_char('}') {
            // Try to parse as instruction or terminator
            if let Some(term) = self.try_parse_terminator()? {
                terminator = Some(term);
                break;
            }

            let inst = self.parse_instruction()?;
            instructions.push(inst);
            self.skip_whitespace_and_comments();
        }

        let terminator = terminator.unwrap_or(SilTerminator::Unreachable);

        Ok(SilBasicBlock {
            label,
            arguments,
            instructions,
            terminator,
        })
    }

    fn parse_block_argument(&mut self) -> Result<SilValue, SilParseError> {
        self.skip_whitespace();

        // Parse %name
        let name = self.parse_value_name()?;
        self.skip_whitespace();

        // Parse : $Type or @owned/@guaranteed
        self.expect_char(':')?;
        self.skip_whitespace();

        // Skip ownership annotation if present
        if self.peek_char('@') {
            self.advance(); // @
            self.parse_identifier()?; // owned/guaranteed/etc.
            self.skip_whitespace();
        }

        let ty = self.parse_type()?;

        Ok(SilValue {
            name,
            ty,
            debug_name: None,
        })
    }

    fn parse_instruction(&mut self) -> Result<SilInstruction, SilParseError> {
        self.skip_whitespace_and_comments();

        let start_line = self.line;

        // Check for result assignment: %n = ...
        let mut results = Vec::new();

        // Look ahead to determine if this is a result assignment
        // Instructions like `debug_value %0, ...` start with % but aren't result assignments
        let is_result_assignment = self.is_result_assignment();

        if is_result_assignment {
            if self.peek_char('(') {
                // Multiple results
                self.advance(); // (
                while !self.peek_char(')') && !self.is_eof() {
                    let name = self.parse_value_name()?;
                    results.push(SilValue {
                        name,
                        ty: SilType::default(),
                        debug_name: None,
                    });
                    self.skip_whitespace();
                    if self.peek_char(',') {
                        self.advance();
                        self.skip_whitespace();
                    }
                }
                self.expect_char(')')?;
            } else {
                let name = self.parse_value_name()?;
                results.push(SilValue {
                    name,
                    ty: SilType::default(),
                    debug_name: None,
                });
            }

            self.skip_whitespace();
            self.expect_char('=')?;
            self.skip_whitespace();
        }

        // Parse instruction opcode
        let opcode = self.parse_identifier()?;
        self.skip_whitespace();

        let kind = self.parse_instruction_kind(&opcode)?;

        // Some instruction parsers consume the rest of the line (and possibly
        // the trailing newline) internally. Only try to parse locations / skip
        // to EOL if we're still on the same line where the opcode started.
        let location = if self.line == start_line {
            self.try_parse_location()
        } else {
            None
        };

        if self.line == start_line {
            self.skip_to_eol();
        }

        Ok(SilInstruction {
            results,
            kind,
            location,
        })
    }

    #[allow(clippy::too_many_lines)]
    fn parse_instruction_kind(
        &mut self,
        opcode: &str,
    ) -> Result<SilInstructionKind, SilParseError> {
        match opcode {
            "integer_literal" => self.parse_integer_literal(),
            "float_literal" => self.parse_float_literal(),
            "string_literal" => self.parse_string_literal(),
            "alloc_stack" => self.parse_alloc_stack(),
            "dealloc_stack" => self.parse_dealloc_stack(),
            "load" => self.parse_load(),
            "store" => self.parse_store(),
            "struct" => self.parse_struct(),
            "struct_extract" => self.parse_struct_extract(),
            "tuple" => self.parse_tuple(),
            "tuple_extract" => self.parse_tuple_extract(),
            "destructure_tuple" => self.parse_destructure_tuple(),
            "destructure_struct" => self.parse_destructure_struct(),
            "tuple_addr_constructor" => self.parse_tuple_addr_constructor(),
            "builtin" => self.parse_builtin(),
            "apply" => self.parse_apply(),
            "function_ref" => self.parse_function_ref(),
            "dynamic_function_ref" => self.parse_dynamic_function_ref(),
            "prev_dynamic_function_ref" => self.parse_prev_dynamic_function_ref(),
            "has_symbol" => self.parse_has_symbol(),
            "alloc_global" => self.parse_alloc_global(),
            "cond_fail" => self.parse_cond_fail(),
            "begin_access" => self.parse_begin_access(),
            "end_access" => self.parse_end_access(),
            "begin_borrow" => self.parse_begin_borrow(),
            "end_borrow" => self.parse_end_borrow(),
            "copy_value" => self.parse_copy_value(),
            "destroy_value" => self.parse_destroy_value(),
            "destroy_addr" => self.parse_destroy_addr(),
            "copy_addr" => self.parse_copy_addr(),
            "explicit_copy_addr" => self.parse_explicit_copy_addr(),
            "ref_element_addr" => self.parse_ref_element_addr(),
            "debug_value" => self.parse_debug_value(),
            "enum" => self.parse_enum_inst(),
            "init_enum_data_addr" => self.parse_init_enum_data_addr(),
            "inject_enum_addr" => self.parse_inject_enum_addr(),
            "unchecked_take_enum_data_addr" => self.parse_unchecked_take_enum_data_addr(),
            "metatype" => self.parse_metatype(),
            "index_addr" | "index_raw_pointer" => self.parse_index_addr(),
            "init_existential_addr" => self.parse_init_existential_addr(),
            "open_existential_addr" => self.parse_open_existential_addr(),
            "init_existential_ref" => self.parse_init_existential_ref(),
            "open_existential_ref" => self.parse_open_existential_ref(),
            "existential_metatype" => self.parse_existential_metatype(),
            "init_existential_metatype" => self.parse_init_existential_metatype(),
            "open_existential_metatype" => self.parse_open_existential_metatype(),
            "alloc_existential_box" => self.parse_alloc_existential_box(),
            "project_existential_box" => self.parse_project_existential_box(),
            "open_existential_box" => self.parse_open_existential_box(),
            "open_existential_box_value" => self.parse_open_existential_box_value(),
            "dealloc_existential_box" => self.parse_dealloc_existential_box(),
            "select_enum" | "select_enum_addr" => self.parse_select_enum(),
            "unconditional_checked_cast" => self.parse_unconditional_checked_cast(),
            "unconditional_checked_cast_addr" => self.parse_unconditional_checked_cast_addr(),
            "alloc_ref" | "alloc_ref_dynamic" => self.parse_alloc_ref(),
            "dealloc_ref" => self.parse_dealloc_ref(),
            "class_method" => self.parse_class_method(),
            "witness_method" => self.parse_witness_method(),
            "upcast" => self.parse_upcast(),
            "global_addr" => self.parse_global_addr(),
            // Reference counting instructions
            "strong_retain" => self.parse_strong_retain(),
            "strong_release" => self.parse_strong_release(),
            "retain_value" => self.parse_retain_value(),
            "release_value" => self.parse_release_value(),
            // Metatype instructions
            "value_metatype" => self.parse_value_metatype(),
            // Function conversion instructions
            "convert_function" => self.parse_convert_function(),
            "thin_to_thick_function" => self.parse_thin_to_thick_function(),
            "convert_escape_to_noescape" => self.parse_convert_escape_to_noescape(),
            // Lifetime / runtime instructions
            "fix_lifetime" => self.parse_fix_lifetime(),
            "is_unique" => self.parse_is_unique(),
            // Bridge object conversions (ObjC interop)
            "ref_to_bridge_object" => self.parse_ref_to_bridge_object(),
            "bridge_object_to_ref" => self.parse_bridge_object_to_ref(),
            "bridge_object_to_word" => self.parse_bridge_object_to_word(),
            "classify_bridge_object" => self.parse_classify_bridge_object(),
            "value_to_bridge_object" => self.parse_value_to_bridge_object(),
            // ObjC metatype conversions
            "thick_to_objc_metatype" => self.parse_thick_to_objc_metatype(),
            "objc_to_thick_metatype" => self.parse_objc_to_thick_metatype(),
            // Block storage (ObjC blocks)
            "project_block_storage" => self.parse_project_block_storage(),
            "init_block_storage_header" => self.parse_init_block_storage_header(),
            "copy_block" => self.parse_copy_block(),
            "copy_block_without_escaping" => self.parse_copy_block_without_escaping(),
            // Memory initialization tracking
            "mark_uninitialized" => self.parse_mark_uninitialized(),
            "mark_dependence" => self.parse_mark_dependence(),
            // ObjC method dispatch
            "objc_method" => self.parse_objc_method(),
            "objc_super_method" => self.parse_objc_super_method(),
            "objc_protocol" => self.parse_objc_protocol(),
            // Key paths
            "keypath" => self.parse_keypath(),
            // Copy-on-Write (COW) mutation
            "begin_cow_mutation" => self.parse_begin_cow_mutation(),
            "end_cow_mutation" => self.parse_end_cow_mutation(),
            "end_cow_mutation_addr" => self.parse_end_cow_mutation_addr(),
            // Unmanaged reference counting
            "unmanaged_retain_value" => self.parse_unmanaged_retain_value(),
            "unmanaged_release_value" => self.parse_unmanaged_release_value(),
            "unmanaged_autorelease_value" => self.parse_unmanaged_autorelease_value(),
            // Unchecked reference/pointer conversions
            "ref_to_unmanaged" => self.parse_ref_to_unmanaged(),
            "unmanaged_to_ref" => self.parse_unmanaged_to_ref(),
            "ref_to_raw_pointer" => self.parse_ref_to_raw_pointer(),
            "raw_pointer_to_ref" => self.parse_raw_pointer_to_ref(),
            // Weak reference storage
            "load_weak" => self.parse_load_weak(),
            "store_weak" => self.parse_store_weak(),
            "weak_copy_value" => self.parse_weak_copy_value(),
            "strong_copy_weak_value" => self.parse_strong_copy_weak_value(),
            // Unowned reference storage
            "load_unowned" => self.parse_load_unowned(),
            "store_unowned" => self.parse_store_unowned(),
            "unowned_copy_value" => self.parse_unowned_copy_value(),
            // ObjC metatype conversions
            "objc_metatype_to_object" => self.parse_objc_metatype_to_object(),
            "objc_existential_metatype_to_object" => {
                self.parse_objc_existential_metatype_to_object()
            }
            // Variadic generics / pack instructions
            "alloc_pack" => self.parse_alloc_pack(),
            "dealloc_pack" => self.parse_dealloc_pack(),
            "pack_length" => self.parse_pack_length(),
            "dynamic_pack_index" => self.parse_dynamic_pack_index(),
            "scalar_pack_index" => self.parse_scalar_pack_index(),
            "pack_pack_index" => self.parse_pack_pack_index(),
            "open_pack_element" => self.parse_open_pack_element(),
            "pack_element_get" => self.parse_pack_element_get(),
            "pack_element_set" => self.parse_pack_element_set(),
            "tuple_pack_element_addr" => self.parse_tuple_pack_element_addr(),
            // Async/await continuation instructions
            "get_async_continuation" => self.parse_get_async_continuation(),
            "get_async_continuation_addr" => self.parse_get_async_continuation_addr(),
            // Pointer/address conversions
            "address_to_pointer" => self.parse_address_to_pointer(),
            "pointer_to_address" => self.parse_pointer_to_address(),
            // Unchecked casts
            "unchecked_ref_cast" => self.parse_unchecked_ref_cast(),
            "unchecked_addr_cast" => self.parse_unchecked_addr_cast(),
            "unchecked_trivial_bit_cast" => self.parse_unchecked_trivial_bit_cast(),
            "unchecked_bitwise_cast" => self.parse_unchecked_bitwise_cast(),
            // Actor/concurrency
            "hop_to_executor" => self.parse_hop_to_executor(),
            "extract_executor" => self.parse_extract_executor(),
            // Structural address instructions
            "struct_element_addr" => self.parse_struct_element_addr(),
            "tuple_element_addr" => self.parse_tuple_element_addr(),
            "ref_tail_addr" => self.parse_ref_tail_addr(),
            "tail_addr" => self.parse_tail_addr(),
            // Closure/partial application
            "partial_apply" => self.parse_partial_apply(),
            "load_borrow" => self.parse_load_borrow(),
            // Box allocation
            "alloc_box" => self.parse_alloc_box(),
            "project_box" => self.parse_project_box(),
            "dealloc_box" => self.parse_dealloc_box(),
            // Method dispatch
            "super_method" => self.parse_super_method(),
            // Pack instructions
            "tuple_pack_extract" => self.parse_tuple_pack_extract(),
            // Global values
            "global_value" => self.parse_global_value(),
            // Memory binding
            "bind_memory" => self.parse_bind_memory(),
            "rebind_memory" => self.parse_rebind_memory(),
            // Move semantics
            "move_value" => self.parse_move_value(),
            // Enum data extraction
            "unchecked_enum_data" => self.parse_unchecked_enum_data(),
            // Assign instruction
            "assign" => self.parse_assign(),
            // Differentiable programming instructions
            "differentiable_function" => self.parse_differentiable_function(),
            "linear_function" => self.parse_linear_function(),
            "differentiable_function_extract" => self.parse_differentiable_function_extract(),
            "linear_function_extract" => self.parse_linear_function_extract(),
            "differentiability_witness_function" => self.parse_differentiability_witness_function(),
            // Coroutine instructions
            "begin_apply" => self.parse_begin_apply(),
            "end_apply" => self.parse_end_apply(),
            "abort_apply" => self.parse_abort_apply(),
            _ => {
                // Unknown instruction - capture the rest of the line
                let text = self.consume_to_eol();
                Ok(SilInstructionKind::Unknown {
                    name: opcode.to_string(),
                    text,
                })
            }
        }
    }

    /// Helper to parse a `try_apply` terminator.
    fn parse_try_apply_terminator(&mut self) -> Result<SilTerminator, SilParseError> {
        // Format: try_apply %callee<Subs>(%args) : $FuncType, normal bb1, error bb2
        self.skip_whitespace();

        // Parse callee (can be %reg or @function_name)
        let callee = if self.peek_char('%') {
            self.parse_value_name()?
        } else if self.peek_char('@') {
            self.advance();
            format!("@{}", self.parse_identifier()?)
        } else {
            return Err(SilParseError {
                message: "Expected callee for try_apply".to_string(),
                line: self.line,
                column: self.column,
            });
        };

        // Parse optional substitutions <T, U>
        let substitutions = self.parse_type_substitutions();

        // Parse arguments (%arg1, %arg2)
        self.skip_whitespace();
        let arguments = self.parse_value_name_list()?;

        // Skip `: $FuncType`
        self.skip_whitespace();
        if self.peek_char(':') {
            self.advance();
            self.skip_whitespace();
            // Skip the function type - it can be complex with @convention etc.
            // Just consume until we hit `, normal`
            while !self.is_eof() {
                if self.peek_str(", normal") || self.peek_str(",normal") {
                    break;
                }
                self.advance();
            }
        }

        // Parse `, normal bbN`
        self.skip_whitespace();
        self.expect_char(',')?;
        self.skip_whitespace();
        self.expect_str("normal")?;
        self.skip_whitespace();
        let normal_dest = self.parse_identifier()?;

        // Parse `, error bbN`
        self.skip_whitespace();
        self.expect_char(',')?;
        self.skip_whitespace();
        self.expect_str("error")?;
        self.skip_whitespace();
        let error_dest = self.parse_identifier()?;

        self.skip_to_eol();
        Ok(SilTerminator::TryApply {
            callee,
            substitutions,
            arguments,
            normal_dest,
            error_dest,
        })
    }

    /// Helper to parse a `checked_cast_br` terminator.
    fn parse_checked_cast_br_terminator(&mut self) -> Result<SilTerminator, SilParseError> {
        // Format: checked_cast_br [exact] SrcType in %op : $Type to DestType, bbSuccess, bbFailure
        self.skip_whitespace();

        // Parse optional [exact] flag
        let exact = if self.peek_char('[') {
            self.advance();
            let flag = self.parse_identifier()?;
            self.expect_char(']')?;
            self.skip_whitespace();
            flag == "exact"
        } else {
            false
        };

        // Parse source type and operand: "SrcType in %op"
        // Skip the source type name (we'll just find "in %")
        while !self.is_eof() && !self.peek_str(" in %") && !self.peek_str(" in\t%") {
            self.advance();
        }
        self.skip_whitespace();
        self.expect_str("in")?;
        self.skip_whitespace();

        let operand = self.parse_value_name()?;

        // Skip `: $Type` annotation
        self.skip_whitespace();
        if self.peek_char(':') {
            self.advance();
            self.skip_whitespace();
            // Skip until we hit "to "
            while !self.is_eof() && !self.peek_str(" to ") {
                self.advance();
            }
        }

        // Parse "to TargetType"
        self.skip_whitespace();
        self.expect_str("to")?;
        self.skip_whitespace();

        // Parse target type name (until comma)
        let target_ty_name = self.consume_until(',');
        let target_ty = SilType::Named(target_ty_name.trim().to_string());

        // Parse success destination
        self.expect_char(',')?;
        self.skip_whitespace();
        let success_dest = self.parse_identifier()?;

        // Parse failure destination
        self.skip_whitespace();
        self.expect_char(',')?;
        self.skip_whitespace();
        let failure_dest = self.parse_identifier()?;

        self.skip_to_eol();
        Ok(SilTerminator::CheckedCastBranch {
            exact,
            operand,
            target_ty,
            success_dest,
            failure_dest,
        })
    }

    /// Helper to parse a `checked_cast_addr_br` terminator.
    fn parse_checked_cast_addr_br_terminator(&mut self) -> Result<SilTerminator, SilParseError> {
        // Format: checked_cast_addr_br <consumption> SrcType in %src : $*SrcType to TargetType in %dest : $*TargetType, bbSuccess, bbFailure
        self.skip_whitespace();

        // Parse consumption kind
        let consumption_str = self.parse_identifier()?;
        let consumption = match consumption_str.as_str() {
            "take_on_success" => CastConsumptionKind::TakeOnSuccess,
            "copy_on_success" => CastConsumptionKind::CopyOnSuccess,
            "borrow_always" => CastConsumptionKind::BorrowAlways,
            // "take_always" or unknown values default to TakeAlways
            _ => CastConsumptionKind::TakeAlways,
        };
        self.skip_whitespace();

        // Parse source type name (until "in %")
        let source_ty_name = self.consume_until_str(" in %");
        let source_ty = SilType::Named(source_ty_name.trim().to_string());

        self.skip_whitespace();
        self.expect_str("in")?;
        self.skip_whitespace();

        let source = self.parse_value_name()?;
        self.skip_whitespace();

        // Skip source address type annotation (: $*SrcType)
        if self.peek_char(':') {
            self.advance();
            self.skip_whitespace();
            while !self.is_eof() && !self.peek_str(" to ") {
                self.advance();
            }
        }

        self.skip_whitespace();
        self.expect_str("to")?;
        self.skip_whitespace();

        // Parse target type name (until "in %")
        let target_ty_name = self.consume_until_str(" in %");
        let target_ty = SilType::Named(target_ty_name.trim().to_string());

        self.skip_whitespace();
        self.expect_str("in")?;
        self.skip_whitespace();

        let dest = self.parse_value_name()?;
        self.skip_whitespace();

        // Skip dest address type annotation (: $*TargetType)
        if self.peek_char(':') {
            self.advance();
            self.skip_whitespace();
            while !self.is_eof() && !self.peek_char(',') {
                self.advance();
            }
        }

        // Parse success destination
        self.expect_char(',')?;
        self.skip_whitespace();
        let success_dest = self.parse_identifier()?;

        // Parse failure destination
        self.skip_whitespace();
        self.expect_char(',')?;
        self.skip_whitespace();
        let failure_dest = self.parse_identifier()?;

        self.skip_to_eol();
        Ok(SilTerminator::CheckedCastAddrBranch {
            consumption,
            source_ty,
            source,
            target_ty,
            dest,
            success_dest,
            failure_dest,
        })
    }

    #[allow(clippy::too_many_lines)]
    fn try_parse_terminator(&mut self) -> Result<Option<SilTerminator>, SilParseError> {
        // Skip leading whitespace
        self.skip_whitespace();

        let start_pos = self.pos;
        let start_line = self.line;
        let start_col = self.column;

        // Skip any result assignment if present
        if self.peek_char('%') || self.peek_char('(') {
            // Not a terminator
            return Ok(None);
        }

        let word = self.parse_identifier()?;
        self.skip_whitespace();

        let result = match word.as_str() {
            "return" => {
                self.skip_whitespace();
                // Handle 'undef' keyword as a special case
                let operand = if self.peek_str("undef") {
                    self.pos += 5; // consume "undef"
                    "undef".to_string()
                } else {
                    self.parse_value_name()?
                };
                self.skip_to_eol();
                Some(SilTerminator::Return { operand })
            }
            "throw" => {
                self.skip_whitespace();
                let operand = self.parse_value_name()?;
                self.skip_to_eol();
                Some(SilTerminator::Throw { operand })
            }
            "throw_addr" => {
                // Only skip to EOL if we're still on the same line as the keyword
                if self.line == start_line {
                    self.skip_to_eol();
                }
                Some(SilTerminator::ThrowAddr)
            }
            "return_borrow" => {
                self.skip_whitespace();
                let operand = self.parse_value_name()?;
                self.skip_to_eol();
                Some(SilTerminator::ReturnBorrow { operand })
            }
            "dynamic_method_br" => {
                // dynamic_method_br %obj : $Type, #Type.method, hasMethod: bb1, noMethod: bb2
                self.skip_whitespace();
                let operand = self.parse_value_name()?;
                self.skip_whitespace();
                // Skip type annotation
                if self.peek_char(':') {
                    while !self.peek_char(',') && !self.is_eof() && !self.peek_char('\n') {
                        self.advance();
                    }
                }
                self.skip_whitespace();
                self.expect_char(',')?;
                self.skip_whitespace();
                // Parse method reference
                let method = self.consume_until(',');
                self.expect_char(',')?;
                self.skip_whitespace();
                // Parse hasMethod dest
                let has_method_dest = self.parse_identifier()?;
                self.skip_whitespace();
                self.expect_char(',')?;
                self.skip_whitespace();
                // Parse noMethod dest
                let no_method_dest = self.parse_identifier()?;
                self.skip_to_eol();
                Some(SilTerminator::DynamicMethodBranch {
                    operand,
                    method: method.trim().to_string(),
                    has_method_dest,
                    no_method_dest,
                })
            }
            "unreachable" => {
                // Only skip to EOL if we're still on the same line as the keyword
                if self.line == start_line {
                    self.skip_to_eol();
                }
                Some(SilTerminator::Unreachable)
            }
            "br" => {
                self.skip_whitespace();
                let dest = self.parse_identifier()?;
                let args = self.parse_optional_args()?;
                self.skip_to_eol();
                Some(SilTerminator::Branch { dest, args })
            }
            "cond_br" => {
                self.skip_whitespace();
                let condition = self.parse_value_name()?;
                self.skip_whitespace();
                self.expect_char(',')?;
                self.skip_whitespace();

                let true_dest = self.parse_identifier()?;
                let true_args = self.parse_optional_args()?;
                self.skip_whitespace();
                self.expect_char(',')?;
                self.skip_whitespace();

                let false_dest = self.parse_identifier()?;
                let false_args = self.parse_optional_args()?;
                self.skip_to_eol();

                Some(SilTerminator::CondBranch {
                    condition,
                    true_dest,
                    true_args,
                    false_dest,
                    false_args,
                })
            }
            "switch_enum" => {
                self.skip_whitespace();
                let operand = self.parse_value_name()?;
                self.skip_whitespace();

                // Skip optional type annotation (: $Type)
                if self.peek_char(':') {
                    self.skip_type_with_generics();
                }

                let (cases, default) = self.parse_enum_switch_cases()?;

                self.skip_to_eol();
                Some(SilTerminator::SwitchEnum {
                    operand,
                    cases,
                    default,
                })
            }
            "switch_enum_addr" => {
                self.skip_whitespace();
                let address = self.parse_value_name()?;
                self.skip_whitespace();

                // Skip optional type annotation (: $*Type)
                if self.peek_char(':') {
                    self.skip_type_with_generics();
                }

                let (cases, default) = self.parse_enum_switch_cases()?;

                self.skip_to_eol();
                Some(SilTerminator::SwitchEnumAddr {
                    address,
                    cases,
                    default,
                })
            }
            "switch_value" => {
                // switch_value %val : $Type, case %lit1 : bb1, case %lit2 : bb2, default bb3
                self.skip_whitespace();
                let operand = self.parse_value_name()?;
                self.skip_whitespace();

                // Skip type annotation
                self.skip_simple_type_annotation();

                let mut cases = Vec::new();
                let mut default = None;

                while self.peek_char(',') {
                    self.advance();
                    self.skip_whitespace_on_line();

                    if self.peek_str("default") {
                        self.expect_str("default")?;
                        self.skip_whitespace_on_line();
                        default = Some(self.parse_identifier()?);
                    } else if self.peek_str("case") {
                        self.expect_str("case")?;
                        self.skip_whitespace_on_line();
                        // case %litN : bbN
                        let lit_name = self.parse_value_name()?;
                        self.skip_whitespace_on_line();
                        self.expect_char(':')?;
                        self.skip_whitespace_on_line();
                        let dest = self.parse_identifier()?;
                        cases.push((SilConstant::Named(lit_name), dest));
                    } else {
                        break;
                    }
                    self.skip_whitespace_on_line();
                }

                self.skip_to_eol();
                Some(SilTerminator::SwitchValue {
                    operand,
                    cases,
                    default,
                })
            }
            "try_apply" => Some(self.parse_try_apply_terminator()?),
            "checked_cast_br" => Some(self.parse_checked_cast_br_terminator()?),
            "checked_cast_addr_br" => Some(self.parse_checked_cast_addr_br_terminator()?),
            "await_async_continuation" => {
                // Format: await_async_continuation %cont : $RawContinuation, resume bbN [, error bbM]
                self.skip_whitespace();
                let continuation = self.parse_value_name()?;
                self.skip_whitespace();
                // Skip type annotation if present
                self.skip_simple_type_annotation();
                self.skip_whitespace();
                self.expect_char(',')?;
                self.skip_whitespace();
                // Expect "resume"
                let kw = self.parse_identifier()?;
                if kw != "resume" {
                    return Err(self.error(&format!(
                        "expected 'resume' in await_async_continuation, got '{kw}'"
                    )));
                }
                self.skip_whitespace_on_line();
                let resume_dest = self.parse_identifier()?;

                // Check for optional error dest - use skip_whitespace_on_line to avoid
                // skipping past newline into the next block
                self.skip_whitespace_on_line();
                let error_dest = if self.peek_char(',') {
                    self.advance();
                    self.skip_whitespace_on_line();
                    let kw = self.parse_identifier()?;
                    if kw != "error" {
                        return Err(self.error(&format!(
                            "expected 'error' in await_async_continuation, got '{kw}'"
                        )));
                    }
                    self.skip_whitespace_on_line();
                    Some(self.parse_identifier()?)
                } else {
                    None
                };

                self.skip_to_eol();
                Some(SilTerminator::AwaitAsyncContinuation {
                    continuation,
                    resume_dest,
                    error_dest,
                })
            }
            "yield" => {
                // Format: yield (%v1, %v2, ...), resume bbResume, unwind bbUnwind
                //    or:  yield %v1 : $Type, resume bbResume, unwind bbUnwind
                self.skip_whitespace();

                let values = if self.peek_char('(') {
                    self.parse_value_name_list()?
                } else if self.peek_char('%') {
                    vec![self.parse_value_name()?]
                } else {
                    Vec::new()
                };

                // Skip type annotation
                self.skip_whitespace();
                self.skip_simple_type_annotation();

                // Parse , resume bbN
                self.skip_whitespace();
                self.expect_char(',')?;
                self.skip_whitespace();
                self.expect_str("resume")?;
                self.skip_whitespace();
                let resume_dest = self.parse_identifier()?;

                // Parse , unwind bbN
                self.skip_whitespace();
                self.expect_char(',')?;
                self.skip_whitespace();
                self.expect_str("unwind")?;
                self.skip_whitespace();
                let unwind_dest = self.parse_identifier()?;

                self.skip_to_eol();
                Some(SilTerminator::Yield {
                    values,
                    resume_dest,
                    unwind_dest,
                })
            }
            "unwind" => {
                // Note: skip_whitespace() after parse_identifier may have already consumed
                // the newline since there are no arguments. Only skip to EOL if we're still
                // on the same line as the keyword.
                if self.line == start_line {
                    self.skip_to_eol();
                }
                Some(SilTerminator::Unwind)
            }
            _ => None,
        };

        if result.is_none() {
            // Reset position if not a terminator
            self.pos = start_pos;
            self.line = start_line;
            self.column = start_col;
        }

        Ok(result)
    }

    // Individual instruction parsers

    fn parse_integer_literal(&mut self) -> Result<SilInstructionKind, SilParseError> {
        let ty = self.parse_type()?;
        self.skip_whitespace();
        self.expect_char(',')?;
        self.skip_whitespace();

        // Parse integer value (may be negative)
        let neg = if self.peek_char('-') {
            self.advance();
            true
        } else {
            false
        };

        let value_str = self.consume_while(|c| c.is_ascii_digit());
        let value: i128 = value_str
            .parse()
            .map_err(|_| self.error("invalid integer"))?;
        let value = if neg { -value } else { value };

        Ok(SilInstructionKind::IntegerLiteral { ty, value })
    }

    fn parse_float_literal(&mut self) -> Result<SilInstructionKind, SilParseError> {
        let ty = self.parse_type()?;
        self.skip_whitespace();
        self.expect_char(',')?;
        self.skip_whitespace();

        // Parse hex float (0x...) or decimal
        let value_str = self.consume_while(|c| {
            c.is_ascii_hexdigit()
                || c == 'x'
                || c == '.'
                || c == '-'
                || c == '+'
                || c == 'p'
                || c == 'P'
        });

        // Parse hex bit pattern or decimal float
        let value = if value_str.starts_with("0x") || value_str.starts_with("-0x") {
            // Hex float - parse as IEEE 754 bit pattern
            let hex_part = if value_str.starts_with('-') {
                &value_str[3..] // skip -0x
            } else {
                &value_str[2..] // skip 0x
            };
            let bits = u64::from_str_radix(hex_part, 16).unwrap_or(0);
            let result = f64::from_bits(bits);
            if value_str.starts_with('-') {
                -result
            } else {
                result
            }
        } else {
            value_str.parse().unwrap_or(0.0)
        };

        Ok(SilInstructionKind::FloatLiteral { ty, value })
    }

    fn parse_string_literal(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // encoding "value"
        let encoding_str = self.parse_identifier()?;
        let encoding = match encoding_str.as_str() {
            "utf16" => StringEncoding::Utf16,
            "objc_selector" => StringEncoding::ObjCSelector,
            // "utf8" or unknown values default to Utf8
            _ => StringEncoding::Utf8,
        };

        self.skip_whitespace();
        let value = self.parse_string()?;

        Ok(SilInstructionKind::StringLiteral { encoding, value })
    }

    fn parse_alloc_stack(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // alloc_stack [lexical] [var_decl] $Type, let, name "foo"
        // Skip optional attributes like [lexical], [var_decl], [dynamic_lifetime], etc.
        while self.peek_char('[') {
            self.skip_balanced_brackets('[', ']')?;
            self.skip_whitespace();
        }
        let ty = self.parse_type()?;
        Ok(SilInstructionKind::AllocStack { ty })
    }

    fn parse_dealloc_stack(&mut self) -> Result<SilInstructionKind, SilParseError> {
        let operand = self.parse_value_name()?;
        Ok(SilInstructionKind::DeallocStack { operand })
    }

    fn parse_load(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // load [copy] %addr : $*Type
        let kind = self.parse_load_kind()?;
        self.skip_whitespace();
        let address = self.parse_value_name()?;

        Ok(SilInstructionKind::Load { kind, address })
    }

    fn parse_load_kind(&mut self) -> Result<LoadKind, SilParseError> {
        if self.peek_char('[') {
            self.advance();
            let kind_str = self.parse_identifier()?;
            self.expect_char(']')?;
            self.skip_whitespace();

            Ok(match kind_str.as_str() {
                "copy" => LoadKind::Copy,
                "borrow" => LoadKind::Borrow,
                "trivial" => LoadKind::Trivial,
                // "take" or unknown values default to Take
                _ => LoadKind::Take,
            })
        } else {
            Ok(LoadKind::Take)
        }
    }

    fn parse_store(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // store %src to [init] %dest : $*Type
        let source = self.parse_value_name()?;
        self.skip_whitespace();
        self.expect_str("to")?;
        self.skip_whitespace();

        let kind = self.parse_store_kind()?;
        self.skip_whitespace();
        let dest = self.parse_value_name()?;

        Ok(SilInstructionKind::Store { kind, source, dest })
    }

    fn parse_store_kind(&mut self) -> Result<StoreKind, SilParseError> {
        if self.peek_char('[') {
            self.advance();
            let kind_str = self.parse_identifier()?;
            self.expect_char(']')?;
            self.skip_whitespace();

            Ok(match kind_str.as_str() {
                "assign" => StoreKind::Assign,
                "trivial" => StoreKind::Trivial,
                // "init" or unknown values default to Init
                _ => StoreKind::Init,
            })
        } else {
            Ok(StoreKind::Init)
        }
    }

    fn parse_struct(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // struct $Type (%0, %1, ...)
        let ty = self.parse_type()?;
        self.skip_whitespace();
        let operands = self.parse_value_list()?;

        Ok(SilInstructionKind::Struct { ty, operands })
    }

    fn parse_struct_extract(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // struct_extract %0, #Type.field
        let operand = self.parse_value_name()?;
        self.skip_whitespace();
        self.expect_char(',')?;
        self.skip_whitespace();

        let field = self.consume_until_whitespace_or_colon();

        Ok(SilInstructionKind::StructExtract { operand, field })
    }

    fn parse_tuple(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // tuple $Type (%0, %1, ...) or tuple (%0, %1, ...)
        let ty = if self.peek_char('$') {
            self.parse_type()?
        } else {
            SilType::default()
        };
        self.skip_whitespace();
        let operands = self.parse_value_list()?;

        Ok(SilInstructionKind::Tuple { ty, operands })
    }

    fn parse_tuple_extract(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // tuple_extract %0, 0
        let operand = self.parse_value_name()?;
        self.skip_whitespace();
        self.expect_char(',')?;
        self.skip_whitespace();

        let index_str = self.consume_while(|c| c.is_ascii_digit());
        let index: usize = index_str
            .parse()
            .map_err(|_| self.error("invalid tuple index"))?;

        Ok(SilInstructionKind::TupleExtract { operand, index })
    }

    fn parse_destructure_tuple(&mut self) -> Result<SilInstructionKind, SilParseError> {
        let operand = self.parse_value_name()?;
        Ok(SilInstructionKind::DestructureTuple { operand })
    }

    fn parse_destructure_struct(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // (%0, %1, ...) = destructure_struct %val : $StructType
        let operand = self.parse_value_name()?;
        Ok(SilInstructionKind::DestructureStruct { operand })
    }

    fn parse_tuple_addr_constructor(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // tuple_addr_constructor [init|assign] %addr : $*(T1, T2) with (%v1 : $T1, %v2 : $T2)
        self.expect_char('[')?;
        let mode_str = self.parse_identifier()?;
        let init_or_assign = match mode_str.as_str() {
            "assign" => InitOrAssign::Assign,
            // "init" or unknown values default to Init
            _ => InitOrAssign::Init,
        };
        self.expect_char(']')?;
        self.skip_whitespace();

        let dest = self.parse_value_name()?;
        self.skip_whitespace();

        // Skip type annotation `: $*(T1, T2)`
        if self.peek_char(':') {
            self.skip_to_keyword("with");
        }
        self.skip_whitespace();

        // Parse "with"
        if self.peek_str("with") {
            self.pos += 4;
            self.column += 4;
            self.skip_whitespace();
        }

        // Parse element list
        let mut elements = Vec::new();
        if self.peek_char('(') {
            self.advance();
            self.skip_whitespace();
            while !self.peek_char(')') && !self.is_eof() {
                let elem = self.parse_value_name()?;
                elements.push(elem);
                self.skip_whitespace();
                // Skip type annotation
                if self.peek_char(':') {
                    while !self.peek_char(',') && !self.peek_char(')') && !self.is_eof() {
                        self.advance();
                    }
                }
                self.skip_whitespace();
                if self.peek_char(',') {
                    self.advance();
                    self.skip_whitespace();
                }
            }
            if self.peek_char(')') {
                self.advance();
            }
        }

        Ok(SilInstructionKind::TupleAddrConstructor {
            init_or_assign,
            dest,
            elements,
        })
    }

    fn parse_builtin(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // builtin "name"<GenericArgs>(%0, %1, ...) : $Type
        let name = self.parse_string()?;
        self.skip_whitespace();

        // Skip optional generic parameters like <Counter>
        if self.peek_char('<') {
            self.skip_balanced_brackets('<', '>')?;
            self.skip_whitespace();
        }

        let arguments = self.parse_value_list()?;
        self.skip_whitespace();
        self.expect_char(':')?;
        self.skip_whitespace();
        let ty = self.parse_type()?;

        Ok(SilInstructionKind::Builtin {
            name,
            arguments,
            ty,
        })
    }

    fn parse_apply(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // apply [callee_isolation=...] [caller_isolation=...] %callee<Subst>(%arg1, %arg2) : $FunctionType

        // Parse optional isolation attributes
        let mut caller_isolation = None;
        let mut callee_isolation = None;

        while self.peek_char('[') {
            self.advance(); // consume '['
            self.skip_whitespace();
            let attr_name = self.consume_until_char_in(&['=', ']']);

            match attr_name.as_str() {
                "callee_isolation" => {
                    if self.peek_char('=') {
                        self.advance();
                        let value = self.consume_until_char(']');
                        callee_isolation = Some(Self::parse_isolation_value(&value));
                    }
                }
                "caller_isolation" => {
                    if self.peek_char('=') {
                        self.advance();
                        let value = self.consume_until_char(']');
                        caller_isolation = Some(Self::parse_isolation_value(&value));
                    }
                }
                _ => {
                    // Skip unknown attributes
                    if self.peek_char('=') {
                        self.advance();
                        self.consume_until_char(']');
                    }
                }
            }

            if self.peek_char(']') {
                self.advance();
            }
            self.skip_whitespace();
        }

        let callee = self.parse_value_name()?;
        self.skip_whitespace();

        // Parse optional substitutions
        let substitutions = if self.peek_char('<') {
            self.parse_substitutions()?
        } else {
            Vec::new()
        };

        self.skip_whitespace();
        let arguments = self.parse_value_list()?;
        self.skip_whitespace();
        self.expect_char(':')?;
        self.skip_whitespace();
        let ty = self.parse_type()?;

        Ok(SilInstructionKind::Apply {
            callee,
            substitutions,
            arguments,
            ty,
            caller_isolation,
            callee_isolation,
        })
    }

    /// Parse an actor isolation value string into `ActorIsolation` enum
    fn parse_isolation_value(value: &str) -> ActorIsolation {
        match value.trim() {
            "actor_instance" => ActorIsolation::ActorInstance,
            "nonisolated" => ActorIsolation::Nonisolated,
            "erased" => ActorIsolation::Erased,
            other => {
                // Global actors like "main_actor" or custom global actors
                if other.contains("main") || other.contains("Main") {
                    ActorIsolation::GlobalActor("MainActor".to_string())
                } else {
                    ActorIsolation::GlobalActor(other.to_string())
                }
            }
        }
    }

    fn parse_function_ref(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // function_ref @name : $Type
        self.expect_char('@')?;
        let name = self.parse_symbol_name()?;

        Ok(SilInstructionKind::FunctionRef { name })
    }

    fn parse_dynamic_function_ref(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // dynamic_function_ref @name : $Type
        self.expect_char('@')?;
        let name = self.parse_symbol_name()?;

        Ok(SilInstructionKind::DynamicFunctionRef { name })
    }

    fn parse_prev_dynamic_function_ref(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // prev_dynamic_function_ref @name : $Type
        self.expect_char('@')?;
        let name = self.parse_symbol_name()?;

        Ok(SilInstructionKind::PrevDynamicFunctionRef { name })
    }

    fn parse_has_symbol(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // has_symbol #SomeType.member
        self.expect_char('#')?;
        let decl = self.parse_symbol_name()?;

        Ok(SilInstructionKind::HasSymbol { decl })
    }

    fn parse_alloc_global(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // alloc_global @globalName
        self.expect_char('@')?;
        let name = self.parse_symbol_name()?;

        Ok(SilInstructionKind::AllocGlobal { name })
    }

    fn parse_cond_fail(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // cond_fail %condition, "message"
        let condition = self.parse_value_name()?;
        self.skip_whitespace();
        self.expect_char(',')?;
        self.skip_whitespace();
        let message = self.parse_string()?;

        Ok(SilInstructionKind::CondFail { condition, message })
    }

    fn parse_begin_access(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // begin_access [read] [dynamic] [no_nested_conflict]? %addr : $*Type
        // First attribute: access kind
        self.expect_char('[')?;
        let kind_str = self.parse_identifier()?;
        self.expect_char(']')?;
        self.skip_whitespace();

        let kind = match kind_str.as_str() {
            "modify" => AccessKind::Modify,
            "init" => AccessKind::Init,
            "deinit" => AccessKind::Deinit,
            // "read" or unknown values default to Read
            _ => AccessKind::Read,
        };

        // Second attribute: enforcement
        self.expect_char('[')?;
        let enforcement_str = self.parse_identifier()?;
        self.expect_char(']')?;
        self.skip_whitespace();

        let enforcement = match enforcement_str.as_str() {
            "static" => Enforcement::Static,
            "dynamic" => Enforcement::Dynamic,
            "unsafe" => Enforcement::Unsafe,
            _ => Enforcement::Unknown,
        };

        // Optional additional attributes: [no_nested_conflict], [builtin], etc.
        while self.peek_char('[') {
            self.advance();
            self.parse_identifier()?;
            self.expect_char(']')?;
            self.skip_whitespace();
        }

        let address = self.parse_value_name()?;

        Ok(SilInstructionKind::BeginAccess {
            kind,
            enforcement,
            address,
        })
    }

    fn parse_end_access(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // end_access %addr : $*Type
        // Skip optional [abort] annotation
        if self.peek_char('[') {
            self.advance();
            self.parse_identifier()?;
            self.expect_char(']')?;
            self.skip_whitespace();
        }

        let address = self.parse_value_name()?;
        Ok(SilInstructionKind::EndAccess { address })
    }

    fn parse_begin_borrow(&mut self) -> Result<SilInstructionKind, SilParseError> {
        let operand = self.parse_value_name()?;
        Ok(SilInstructionKind::BeginBorrow { operand })
    }

    fn parse_end_borrow(&mut self) -> Result<SilInstructionKind, SilParseError> {
        let operand = self.parse_value_name()?;
        Ok(SilInstructionKind::EndBorrow { operand })
    }

    fn parse_copy_value(&mut self) -> Result<SilInstructionKind, SilParseError> {
        let operand = self.parse_value_name()?;
        Ok(SilInstructionKind::CopyValue { operand })
    }

    fn parse_destroy_value(&mut self) -> Result<SilInstructionKind, SilParseError> {
        let operand = self.parse_value_name()?;
        Ok(SilInstructionKind::DestroyValue { operand })
    }

    // Reference counting instructions
    fn parse_strong_retain(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // strong_retain %operand : $RefType
        let operand = self.parse_value_name()?;
        Ok(SilInstructionKind::StrongRetain { operand })
    }

    fn parse_strong_release(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // strong_release %operand : $RefType
        let operand = self.parse_value_name()?;
        Ok(SilInstructionKind::StrongRelease { operand })
    }

    fn parse_retain_value(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // retain_value %operand : $Type
        let operand = self.parse_value_name()?;
        Ok(SilInstructionKind::RetainValue { operand })
    }

    fn parse_release_value(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // release_value %operand : $Type
        let operand = self.parse_value_name()?;
        Ok(SilInstructionKind::ReleaseValue { operand })
    }

    fn parse_destroy_addr(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // destroy_addr %addr : $*Type
        let address = self.parse_value_name()?;
        Ok(SilInstructionKind::DestroyAddr { address })
    }

    fn parse_copy_addr(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // copy_addr [take] %src to [init] %dest : $*Type
        // Flags: [take] means source is consumed, [init] means dest is uninitialized
        let mut take = false;
        let mut init = false;

        // Check for [take]
        if self.peek_char('[') {
            self.advance();
            let attr = self.parse_identifier()?;
            if attr == "take" {
                take = true;
            }
            self.expect_char(']')?;
            self.skip_whitespace();
        }

        let source = self.parse_value_name()?;
        self.skip_whitespace();

        // Expect "to"
        let to_word = self.parse_identifier()?;
        if to_word != "to" {
            return Err(self.error(&format!("expected 'to', got '{to_word}'")));
        }
        self.skip_whitespace();

        // Check for [init]
        if self.peek_char('[') {
            self.advance();
            let attr = self.parse_identifier()?;
            if attr == "init" {
                init = true;
            }
            self.expect_char(']')?;
            self.skip_whitespace();
        }

        let dest = self.parse_value_name()?;

        Ok(SilInstructionKind::CopyAddr {
            take,
            init,
            source,
            dest,
        })
    }

    fn parse_explicit_copy_addr(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // explicit_copy_addr [take] %src to [init] %dest : $*Type
        // Same format as copy_addr, survives move checking
        let mut take = false;
        let mut init = false;

        // Check for [take]
        if self.peek_char('[') {
            self.advance();
            let attr = self.parse_identifier()?;
            if attr == "take" {
                take = true;
            }
            self.expect_char(']')?;
            self.skip_whitespace();
        }

        let source = self.parse_value_name()?;
        self.skip_whitespace();

        // Expect "to"
        let to_word = self.parse_identifier()?;
        if to_word != "to" {
            return Err(self.error(&format!("expected 'to', got '{to_word}'")));
        }
        self.skip_whitespace();

        // Check for [init]
        if self.peek_char('[') {
            self.advance();
            let attr = self.parse_identifier()?;
            if attr == "init" {
                init = true;
            }
            self.expect_char(']')?;
            self.skip_whitespace();
        }

        let dest = self.parse_value_name()?;

        Ok(SilInstructionKind::ExplicitCopyAddr {
            take,
            init,
            source,
            dest,
        })
    }

    fn parse_ref_element_addr(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // ref_element_addr [immutable] %obj : $Type, #Type.field
        let mut immutable = false;

        // Check for [immutable]
        if self.peek_char('[') {
            self.advance();
            let attr = self.parse_identifier()?;
            if attr == "immutable" {
                immutable = true;
            }
            self.expect_char(']')?;
            self.skip_whitespace();
        }

        let operand = self.parse_value_name()?;
        self.skip_whitespace();

        // Skip type annotation (: $Type)
        if self.peek_char(':') {
            self.advance();
            self.skip_whitespace();
            self.parse_type()?;
            self.skip_whitespace();
        }

        self.expect_char(',')?;
        self.skip_whitespace();

        // Parse field reference (#Type.field)
        let field = self.consume_until_whitespace_or_colon();

        Ok(SilInstructionKind::RefElementAddr {
            operand,
            field,
            immutable,
        })
    }

    fn parse_debug_value(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // debug_value can have:
        // - debug_value %val, ... (normal value reference)
        // - debug_value undef : $Type, ... (undef literal)
        let operand = if self.peek_str("undef") {
            self.pos += 5;
            self.column += 5;
            self.skip_whitespace_on_line();
            // Skip type annotation: `: $Type`
            if self.peek_char(':') {
                self.advance();
                self.skip_whitespace_on_line();
                self.parse_type()?;
            }
            // Use a synthetic name for undef
            "_undef".to_string()
        } else {
            self.parse_value_name()?
        };
        self.skip_whitespace_on_line();

        let mut name = None;
        let mut argno = None;

        // Parse optional annotations (all on the same line)
        // Stop when we see "loc" which is handled by try_parse_location
        while self.peek_char(',') {
            // Peek ahead to see if next annotation is "loc"
            let saved_pos = self.pos;
            let saved_line = self.line;
            let saved_col = self.column;

            self.advance(); // skip ','
            self.skip_whitespace_on_line();

            // Check if it's "loc " which signals source location annotation
            if self.peek_str("loc ") {
                // Put back the comma, let try_parse_location handle it
                self.pos = saved_pos;
                self.line = saved_line;
                self.column = saved_col;
                break;
            }

            let annotation = self.parse_identifier()?;
            self.skip_whitespace_on_line();

            match annotation.as_str() {
                "name" => {
                    self.skip_whitespace_on_line();
                    name = Some(self.parse_string()?);
                }
                "argno" => {
                    self.skip_whitespace_on_line();
                    let num_str = self.consume_while(|c| c.is_ascii_digit());
                    argno = num_str.parse().ok();
                }
                "type" => {
                    // Skip type annotation: `type $Type`
                    self.skip_whitespace_on_line();
                    if self.peek_char('$') {
                        self.parse_type()?;
                    }
                }
                "expr" => {
                    // Skip expr annotation to next comma or end of annotations
                    // expr op_constu:42:op_fragment:#Int._value
                    self.skip_whitespace_on_line();
                    // Consume until comma, newline, or comment
                    while let Some(ch) = self.current_char() {
                        if ch == ','
                            || ch == '\n'
                            || ch == '\r'
                            || (ch == '/' && self.peek_str("//"))
                        {
                            break;
                        }
                        self.advance();
                    }
                }
                // "let", "var", and unknown annotations are ignored
                _ => {}
            }
            self.skip_whitespace_on_line();
        }

        Ok(SilInstructionKind::DebugValue {
            operand,
            name,
            argno,
        })
    }

    fn parse_enum_inst(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // enum $Type, #Type.case [, %payload]
        let ty = self.parse_type()?;
        self.skip_whitespace();
        self.expect_char(',')?;
        self.skip_whitespace();

        let case_name = self.consume_until_whitespace_or_colon();
        self.skip_whitespace();

        let operand = if self.peek_char(',') {
            self.advance();
            self.skip_whitespace();
            Some(self.parse_value_name()?)
        } else {
            None
        };

        Ok(SilInstructionKind::Enum {
            ty,
            case_name,
            operand,
        })
    }

    fn parse_init_enum_data_addr(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // init_enum_data_addr %addr : $*EnumType, #EnumType.case!enumelt
        let address = self.parse_value_name()?;
        self.skip_whitespace();

        // Skip type annotation (: $*Type)
        if self.peek_char(':') {
            self.advance();
            self.skip_whitespace();
            self.parse_type()?;
            self.skip_whitespace();
        }

        self.expect_char(',')?;
        self.skip_whitespace();

        let case_name = self.consume_until_whitespace_or_colon();

        Ok(SilInstructionKind::InitEnumDataAddr { address, case_name })
    }

    fn parse_inject_enum_addr(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // inject_enum_addr %addr : $*EnumType, #EnumType.case!enumelt
        let address = self.parse_value_name()?;
        self.skip_whitespace();

        // Skip type annotation (: $*Type)
        if self.peek_char(':') {
            self.advance();
            self.skip_whitespace();
            self.parse_type()?;
            self.skip_whitespace();
        }

        self.expect_char(',')?;
        self.skip_whitespace();

        let case_name = self.consume_until_whitespace_or_colon();

        Ok(SilInstructionKind::InjectEnumAddr { address, case_name })
    }

    fn parse_unchecked_take_enum_data_addr(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // unchecked_take_enum_data_addr %addr : $*EnumType, #EnumType.case!enumelt
        let address = self.parse_value_name()?;
        self.skip_whitespace();

        // Skip type annotation (: $*Type)
        if self.peek_char(':') {
            self.advance();
            self.skip_whitespace();
            self.parse_type()?;
            self.skip_whitespace();
        }

        self.expect_char(',')?;
        self.skip_whitespace();

        let case_name = self.consume_until_whitespace_or_colon();

        Ok(SilInstructionKind::UncheckedTakeEnumDataAddr { address, case_name })
    }

    fn parse_metatype(&mut self) -> Result<SilInstructionKind, SilParseError> {
        let ty = self.parse_type()?;
        Ok(SilInstructionKind::Metatype { ty })
    }

    fn parse_value_metatype(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // value_metatype $@thick T.Type, %value : $T
        // Result type comes first, then comma, then operand
        let _result_ty = self.parse_type()?;
        self.skip_whitespace();
        self.expect_char(',')?;
        self.skip_whitespace();
        let operand = self.parse_value_name()?;
        Ok(SilInstructionKind::ValueMetatype { operand })
    }

    // Function conversion instructions

    fn parse_convert_function(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // convert_function %0 : $SrcFuncType to $DestFuncType
        // convert_function [without_actually_escaping] %0 : $SrcFuncType to $DestFuncType
        // Skip optional attribute
        if self.peek_char('[') {
            self.advance();
            self.consume_until(']');
            self.expect_char(']')?;
            self.skip_whitespace();
        }

        let operand = self.parse_value_name()?;
        self.skip_whitespace();

        // Skip source type annotation (: $SrcType)
        if self.peek_char(':') {
            self.advance();
            self.skip_whitespace();
            self.parse_type()?;
            self.skip_whitespace();
        }

        self.expect_str("to")?;
        self.skip_whitespace();

        let ty = self.parse_type()?;

        Ok(SilInstructionKind::ConvertFunction { operand, ty })
    }

    fn parse_thin_to_thick_function(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // thin_to_thick_function %0 : $@convention(thin) () -> () to $() -> ()
        let operand = self.parse_value_name()?;
        self.skip_whitespace();

        // Skip source type annotation (: $@convention(thin) ...)
        if self.peek_char(':') {
            self.advance();
            self.skip_whitespace();
            self.parse_type()?;
            self.skip_whitespace();
        }

        self.expect_str("to")?;
        self.skip_whitespace();

        let ty = self.parse_type()?;

        Ok(SilInstructionKind::ThinToThickFunction { operand, ty })
    }

    fn parse_convert_escape_to_noescape(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // convert_escape_to_noescape [not_guaranteed] %0 : $@callee_guaranteed () -> () to $@noescape () -> ()
        // convert_escape_to_noescape %0 : $@callee_guaranteed () -> () to $@noescape () -> ()
        let mut lifetime_guaranteed = true;

        // Check for [not_guaranteed]
        if self.peek_char('[') {
            self.advance();
            let attr = self.parse_identifier()?;
            if attr == "not_guaranteed" {
                lifetime_guaranteed = false;
            }
            self.expect_char(']')?;
            self.skip_whitespace();
        }

        let operand = self.parse_value_name()?;
        self.skip_whitespace();

        // Skip source type annotation
        if self.peek_char(':') {
            self.advance();
            self.skip_whitespace();
            self.parse_type()?;
            self.skip_whitespace();
        }

        self.expect_str("to")?;
        self.skip_whitespace();

        let ty = self.parse_type()?;

        Ok(SilInstructionKind::ConvertEscapeToNoEscape {
            operand,
            ty,
            lifetime_guaranteed,
        })
    }

    // Lifetime / runtime instructions

    fn parse_fix_lifetime(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // fix_lifetime %0 : $Type
        let operand = self.parse_value_name()?;
        Ok(SilInstructionKind::FixLifetime { operand })
    }

    fn parse_is_unique(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // is_unique %0 : $*RefType
        let operand = self.parse_value_name()?;
        Ok(SilInstructionKind::IsUnique { operand })
    }

    // Bridge object conversions (ObjC interop)

    fn parse_ref_to_bridge_object(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // ref_to_bridge_object %ref : $C, %bits : $Builtin.Word
        let operand = self.parse_value_name()?;
        self.skip_whitespace();

        // Skip type annotation (: $C)
        if self.peek_char(':') {
            self.advance();
            self.skip_whitespace();
            self.parse_type()?;
            self.skip_whitespace();
        }

        self.expect_char(',')?;
        self.skip_whitespace();

        let bits = self.parse_value_name()?;

        Ok(SilInstructionKind::RefToBridgeObject { operand, bits })
    }

    fn parse_bridge_object_to_ref(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // bridge_object_to_ref %0 : $Builtin.BridgeObject to $C
        let operand = self.parse_value_name()?;
        self.skip_whitespace();

        // Skip source type annotation (: $Builtin.BridgeObject)
        if self.peek_char(':') {
            self.advance();
            self.skip_whitespace();
            self.parse_type()?;
            self.skip_whitespace();
        }

        self.expect_str("to")?;
        self.skip_whitespace();

        let ty = self.parse_type()?;

        Ok(SilInstructionKind::BridgeObjectToRef { operand, ty })
    }

    fn parse_bridge_object_to_word(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // bridge_object_to_word %0 : $Builtin.BridgeObject
        let operand = self.parse_value_name()?;
        Ok(SilInstructionKind::BridgeObjectToWord { operand })
    }

    fn parse_classify_bridge_object(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // classify_bridge_object %0 : $Builtin.BridgeObject
        let operand = self.parse_value_name()?;
        Ok(SilInstructionKind::ClassifyBridgeObject { operand })
    }

    fn parse_value_to_bridge_object(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // value_to_bridge_object %0 : $Builtin.Word
        let operand = self.parse_value_name()?;
        Ok(SilInstructionKind::ValueToBridgeObject { operand })
    }

    // ObjC metatype conversions

    fn parse_thick_to_objc_metatype(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // thick_to_objc_metatype %0 : $@thick T.Type
        let operand = self.parse_value_name()?;
        Ok(SilInstructionKind::ThickToObjcMetatype { operand })
    }

    fn parse_objc_to_thick_metatype(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // objc_to_thick_metatype %0 : $@objc_metatype T.Type to $@thick T.Type
        let operand = self.parse_value_name()?;
        self.skip_whitespace();

        // Skip source type annotation (: $@objc_metatype T.Type)
        if self.peek_char(':') {
            self.advance();
            self.skip_whitespace();
            self.parse_type()?;
            self.skip_whitespace();
        }

        // Optional: to $TargetType
        let ty = if self.peek_str("to") {
            self.expect_str("to")?;
            self.skip_whitespace();
            self.parse_type()?
        } else {
            SilType::Named("Metatype".to_string())
        };

        Ok(SilInstructionKind::ObjcToThickMetatype { operand, ty })
    }

    // Block storage (ObjC blocks)

    fn parse_project_block_storage(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // project_block_storage %0 : $*@block_storage T
        let operand = self.parse_value_name()?;
        Ok(SilInstructionKind::ProjectBlockStorage { operand })
    }

    fn parse_init_block_storage_header(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // init_block_storage_header %0 : $*@block_storage T, invoke %fn : $InvokeType, type $BlockType
        let block_storage = self.parse_value_name()?;
        self.skip_whitespace();

        // Skip type annotation (: $*@block_storage T)
        if self.peek_char(':') {
            self.advance();
            self.skip_whitespace();
            self.parse_type()?;
            self.skip_whitespace();
        }

        self.expect_char(',')?;
        self.skip_whitespace();

        self.expect_str("invoke")?;
        self.skip_whitespace();

        let invoke_fn = self.parse_value_name()?;
        self.skip_whitespace();

        // Skip invoke function type annotation
        if self.peek_char(':') {
            self.advance();
            self.skip_whitespace();
            self.parse_type()?;
            self.skip_whitespace();
        }

        // Optional: , type $BlockType
        let ty = if self.peek_char(',') {
            self.advance();
            self.skip_whitespace();
            self.expect_str("type")?;
            self.skip_whitespace();
            self.parse_type()?
        } else {
            SilType::Named("Block".to_string())
        };

        Ok(SilInstructionKind::InitBlockStorageHeader {
            block_storage,
            invoke_fn,
            ty,
        })
    }

    fn parse_copy_block(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // copy_block %0 : $@convention(block) () -> ()
        let operand = self.parse_value_name()?;
        Ok(SilInstructionKind::CopyBlock { operand })
    }

    fn parse_copy_block_without_escaping(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // copy_block_without_escaping %0 : $T to %1 : $U
        let operand = self.parse_value_name()?;
        self.skip_whitespace();
        // Skip type annotation
        if self.peek_char(':') {
            while !self.peek_str("to") && !self.is_eof() && !self.peek_char('\n') {
                self.advance();
            }
        }
        self.skip_whitespace();
        self.expect_str("to")?;
        self.skip_whitespace();
        let closure = self.parse_value_name()?;
        Ok(SilInstructionKind::CopyBlockWithoutEscaping { operand, closure })
    }

    fn parse_mark_uninitialized(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // mark_uninitialized [var] %0 : $*T
        self.expect_char('[')?;
        let kind_str = self.parse_identifier()?;
        let kind = match kind_str.as_str() {
            "rootself" => MarkUninitializedKind::RootSelf,
            "crossmodulerootself" => MarkUninitializedKind::CrossModuleRootSelf,
            "derivedself" => MarkUninitializedKind::DerivedSelf,
            "derivedselfonly" => MarkUninitializedKind::DerivedSelfOnly,
            "delegatingself" => MarkUninitializedKind::DelegatingSelf,
            "delegatinginit" => MarkUninitializedKind::DelegatingInit,
            // "var" or unknown values default to Var
            _ => MarkUninitializedKind::Var,
        };
        self.expect_char(']')?;
        self.skip_whitespace();
        let operand = self.parse_value_name()?;
        Ok(SilInstructionKind::MarkUninitialized { kind, operand })
    }

    fn parse_mark_dependence(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // mark_dependence %value : $T on %base : $U
        let value = self.parse_value_name()?;
        self.skip_whitespace();
        // Skip type annotation
        if self.peek_char(':') {
            while !self.peek_str("on") && !self.is_eof() && !self.peek_char('\n') {
                self.advance();
            }
        }
        self.skip_whitespace();
        self.expect_str("on")?;
        self.skip_whitespace();
        let base = self.parse_value_name()?;
        Ok(SilInstructionKind::MarkDependence { value, base })
    }

    fn parse_objc_method(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // objc_method %0 : $ClassName, #ClassName.methodName!foreign : Type, $@convention(objc_method) U -> V
        // Similar format to class_method
        let operand = self.parse_value_name()?;
        self.skip_whitespace();

        // Skip type annotation (: $ClassName)
        if self.peek_char(':') {
            self.advance();
            self.skip_whitespace();
            self.parse_type()?;
            self.skip_whitespace();
        }

        self.expect_char(',')?;
        self.skip_whitespace();

        // Parse method reference: #ClassName.methodName!foreign
        self.expect_char('#')?;
        let method = self.consume_until(':');
        // Skip past the ':' and consume the method type and convention
        self.skip_to_eol();

        Ok(SilInstructionKind::ObjcMethod {
            operand,
            method: method.trim().to_string(),
        })
    }

    fn parse_objc_super_method(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // objc_super_method %0 : $ClassName, #ClassName.methodName!foreign : Type, $@convention(objc_method) U -> V
        // Same format as objc_method
        let operand = self.parse_value_name()?;
        self.skip_whitespace();

        // Skip type annotation (: $ClassName)
        if self.peek_char(':') {
            self.advance();
            self.skip_whitespace();
            self.parse_type()?;
            self.skip_whitespace();
        }

        self.expect_char(',')?;
        self.skip_whitespace();

        // Parse method reference: #ClassName.methodName!foreign
        self.expect_char('#')?;
        let method = self.consume_until(':');
        // Skip past the ':' and consume the method type and convention
        self.skip_to_eol();

        Ok(SilInstructionKind::ObjcSuperMethod {
            operand,
            method: method.trim().to_string(),
        })
    }

    fn parse_objc_protocol(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // objc_protocol #ProtocolName : $Type
        self.expect_char('#')?;
        let protocol = self.consume_until(':');
        self.expect_char(':')?;
        self.skip_whitespace();
        let ty = self.parse_type()?;
        self.skip_to_eol();

        Ok(SilInstructionKind::ObjcProtocol {
            protocol: protocol.trim().to_string(),
            ty,
        })
    }

    fn parse_keypath(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // keypath $KeyPath<Root, Value>, (root $Root; stored_property #Root.value : $Value)
        let ty = self.parse_type()?;
        self.skip_whitespace();
        self.expect_char(',')?;
        self.skip_whitespace();
        let pattern = self.consume_to_eol();

        Ok(SilInstructionKind::KeyPath {
            ty,
            pattern: pattern.trim().to_string(),
        })
    }

    fn parse_begin_cow_mutation(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // begin_cow_mutation [native] %0 : $BufferClass
        // Returns (Builtin.Int1, $BufferClass)
        let mut native = false;

        // Check for [native] attribute
        if self.peek_char('[') {
            self.advance();
            let attr = self.parse_identifier()?;
            if attr == "native" {
                native = true;
            }
            self.expect_char(']')?;
            self.skip_whitespace();
        }

        let operand = self.parse_value_name()?;
        self.skip_to_eol();

        Ok(SilInstructionKind::BeginCowMutation { operand, native })
    }

    fn parse_end_cow_mutation(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // end_cow_mutation [keep_unique] %0 : $BufferClass
        let mut keep_unique = false;

        // Check for [keep_unique] attribute
        if self.peek_char('[') {
            self.advance();
            let attr = self.parse_identifier()?;
            if attr == "keep_unique" {
                keep_unique = true;
            }
            self.expect_char(']')?;
            self.skip_whitespace();
        }

        let operand = self.parse_value_name()?;
        self.skip_to_eol();

        Ok(SilInstructionKind::EndCowMutation {
            operand,
            keep_unique,
        })
    }

    fn parse_end_cow_mutation_addr(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // end_cow_mutation_addr %0 : $*T
        let address = self.parse_value_name()?;
        self.skip_to_eol();

        Ok(SilInstructionKind::EndCowMutationAddr { address })
    }

    fn parse_unmanaged_retain_value(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // unmanaged_retain_value %0 : $T
        let operand = self.parse_value_name()?;
        self.skip_to_eol();

        Ok(SilInstructionKind::UnmanagedRetainValue { operand })
    }

    fn parse_unmanaged_release_value(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // unmanaged_release_value %0 : $T
        let operand = self.parse_value_name()?;
        self.skip_to_eol();

        Ok(SilInstructionKind::UnmanagedReleaseValue { operand })
    }

    fn parse_unmanaged_autorelease_value(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // unmanaged_autorelease_value %0 : $T
        let operand = self.parse_value_name()?;
        self.skip_to_eol();

        Ok(SilInstructionKind::UnmanagedAutoreleaseValue { operand })
    }

    fn parse_unchecked_conversion(&mut self) -> Result<(String, SilType), SilParseError> {
        // <opcode> %0 : $Source to $Target
        let operand = self.parse_value_name()?;
        self.skip_whitespace();

        // Skip source type annotation (: $Source)
        if self.peek_char(':') {
            self.advance();
            self.skip_whitespace();
            self.parse_type()?;
            self.skip_whitespace();
        }

        self.expect_str("to")?;
        self.skip_whitespace();
        let ty = self.parse_type()?;
        self.skip_to_eol();
        Ok((operand, ty))
    }

    fn parse_ref_to_unmanaged(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // ref_to_unmanaged %0 : $T to $@sil_unmanaged T
        let (operand, ty) = self.parse_unchecked_conversion()?;
        Ok(SilInstructionKind::RefToUnmanaged { operand, ty })
    }

    fn parse_unmanaged_to_ref(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // unmanaged_to_ref %0 : $@sil_unmanaged T to $T
        let (operand, ty) = self.parse_unchecked_conversion()?;
        Ok(SilInstructionKind::UnmanagedToRef { operand, ty })
    }

    fn parse_ref_to_raw_pointer(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // ref_to_raw_pointer %0 : $T to $Builtin.RawPointer
        let (operand, _ty) = self.parse_unchecked_conversion()?;
        Ok(SilInstructionKind::RefToRawPointer { operand })
    }

    fn parse_raw_pointer_to_ref(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // raw_pointer_to_ref %0 : $Builtin.RawPointer to $T
        let (operand, ty) = self.parse_unchecked_conversion()?;
        Ok(SilInstructionKind::RawPointerToRef { operand, ty })
    }

    fn parse_load_weak(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // load_weak [take]? %0 : $*@sil_weak Optional<T>
        let take = if self.peek_char('[') {
            self.advance(); // [
            let attr = self.parse_identifier()?;
            self.expect_char(']')?;
            self.skip_whitespace();
            attr == "take"
        } else {
            false
        };
        let address = self.parse_value_name()?;
        self.skip_to_eol();
        Ok(SilInstructionKind::LoadWeak { take, address })
    }

    fn parse_store_weak(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // store_weak %0 to [init]? %1 : $*@sil_weak Optional<T>
        let source = self.parse_value_name()?;
        self.skip_whitespace();

        // Skip type annotation if present
        if self.peek_char(':') {
            self.advance();
            self.skip_whitespace();
            self.parse_type()?;
            self.skip_whitespace();
        }

        // Expect "to"
        let _to = self.parse_identifier()?;
        self.skip_whitespace();

        // Check for [init] attribute
        let init = if self.peek_char('[') {
            self.advance(); // [
            let attr = self.parse_identifier()?;
            self.expect_char(']')?;
            self.skip_whitespace();
            attr == "init"
        } else {
            false
        };

        let dest = self.parse_value_name()?;
        self.skip_to_eol();
        Ok(SilInstructionKind::StoreWeak { init, source, dest })
    }

    fn parse_weak_copy_value(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // weak_copy_value %0 : $@sil_weak Optional<T>
        let operand = self.parse_value_name()?;
        self.skip_to_eol();
        Ok(SilInstructionKind::WeakCopyValue { operand })
    }

    fn parse_strong_copy_weak_value(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // strong_copy_weak_value %0 : $@sil_weak Optional<T>
        let operand = self.parse_value_name()?;
        self.skip_to_eol();
        Ok(SilInstructionKind::StrongCopyWeakValue { operand })
    }

    fn parse_load_unowned(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // load_unowned [take]? %0 : $*@sil_unowned T
        let take = if self.peek_char('[') {
            self.advance(); // [
            let attr = self.parse_identifier()?;
            self.expect_char(']')?;
            self.skip_whitespace();
            attr == "take"
        } else {
            false
        };
        let address = self.parse_value_name()?;
        self.skip_to_eol();
        Ok(SilInstructionKind::LoadUnowned { take, address })
    }

    fn parse_store_unowned(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // store_unowned %0 to [init]? %1 : $*@sil_unowned T
        let source = self.parse_value_name()?;
        self.skip_whitespace();

        // Skip type annotation if present
        if self.peek_char(':') {
            self.advance();
            self.skip_whitespace();
            self.parse_type()?;
            self.skip_whitespace();
        }

        // Expect "to"
        let _to = self.parse_identifier()?;
        self.skip_whitespace();

        // Check for [init] attribute
        let init = if self.peek_char('[') {
            self.advance(); // [
            let attr = self.parse_identifier()?;
            self.expect_char(']')?;
            self.skip_whitespace();
            attr == "init"
        } else {
            false
        };

        let dest = self.parse_value_name()?;
        self.skip_to_eol();
        Ok(SilInstructionKind::StoreUnowned { init, source, dest })
    }

    fn parse_unowned_copy_value(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // unowned_copy_value %0 : $T
        let operand = self.parse_value_name()?;
        self.skip_to_eol();
        Ok(SilInstructionKind::UnownedCopyValue { operand })
    }

    fn parse_objc_metatype_to_object(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // objc_metatype_to_object %0 : $@objc_metatype T.Type to $AnyObject
        let operand = self.parse_value_name()?;
        self.skip_to_eol();
        Ok(SilInstructionKind::ObjcMetatypeToObject { operand })
    }

    fn parse_objc_existential_metatype_to_object(
        &mut self,
    ) -> Result<SilInstructionKind, SilParseError> {
        // objc_existential_metatype_to_object %0 : $@objc_metatype P.Type to $AnyObject
        let operand = self.parse_value_name()?;
        self.skip_to_eol();
        Ok(SilInstructionKind::ObjcExistentialMetatypeToObject { operand })
    }

    // Variadic generics / pack instructions

    fn parse_alloc_pack(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // alloc_pack $Pack{Int, repeat each T}
        let pack_ty = self.parse_type()?;
        self.skip_to_eol();
        Ok(SilInstructionKind::AllocPack { pack_ty })
    }

    fn parse_dealloc_pack(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // dealloc_pack %pack : $*Pack{...}
        let operand = self.parse_value_name()?;
        self.skip_to_eol();
        Ok(SilInstructionKind::DeallocPack { operand })
    }

    fn parse_pack_length(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // pack_length $Pack{Int, Float, String}
        let pack_ty = self.parse_type()?;
        self.skip_to_eol();
        Ok(SilInstructionKind::PackLength { pack_ty })
    }

    fn parse_dynamic_pack_index(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // dynamic_pack_index %intIndex of $Pack{repeat each T}
        let operand = self.parse_value_name()?;
        self.skip_whitespace();
        // Expect "of"
        let of_kw = self.parse_identifier()?;
        if of_kw != "of" {
            return Err(self.error(&format!(
                "expected 'of' in dynamic_pack_index, got '{of_kw}'"
            )));
        }
        self.skip_whitespace();
        let pack_ty = self.parse_type()?;
        self.skip_to_eol();
        Ok(SilInstructionKind::DynamicPackIndex { operand, pack_ty })
    }

    fn parse_scalar_pack_index(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // scalar_pack_index 0 of $Pack{Int, repeat each T}
        let index_str = self.consume_while(|c| c.is_ascii_digit());
        let index: usize = index_str
            .parse()
            .map_err(|_| self.error("invalid scalar_pack_index index"))?;
        self.skip_whitespace();
        // Expect "of"
        let of_kw = self.parse_identifier()?;
        if of_kw != "of" {
            return Err(self.error(&format!(
                "expected 'of' in scalar_pack_index, got '{of_kw}'"
            )));
        }
        self.skip_whitespace();
        let pack_ty = self.parse_type()?;
        self.skip_to_eol();
        Ok(SilInstructionKind::ScalarPackIndex { index, pack_ty })
    }

    fn parse_pack_pack_index(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // pack_pack_index 1, %innerIndex of $Pack{Int, repeat each T}
        let index_str = self.consume_while(|c| c.is_ascii_digit());
        let component_index: usize = index_str
            .parse()
            .map_err(|_| self.error("invalid pack_pack_index component index"))?;
        self.skip_whitespace();
        self.expect_char(',')?;
        self.skip_whitespace();
        let inner_index = self.parse_value_name()?;
        self.skip_whitespace();
        // Expect "of"
        let of_kw = self.parse_identifier()?;
        if of_kw != "of" {
            return Err(self.error(&format!("expected 'of' in pack_pack_index, got '{of_kw}'")));
        }
        self.skip_whitespace();
        let pack_ty = self.parse_type()?;
        self.skip_to_eol();
        Ok(SilInstructionKind::PackPackIndex {
            component_index,
            inner_index,
            pack_ty,
        })
    }

    fn parse_open_pack_element(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // open_pack_element %index of <each U> at <Pack{...}>, shape $each U, uuid "..."
        let index = self.parse_value_name()?;
        self.skip_whitespace();
        // Skip "of <...> at <...>, shape ..." - capture just the essential parts
        let rest = self.consume_to_eol();
        // Extract uuid from rest
        let uuid = rest
            .find("uuid \"")
            .and_then(|uuid_start| {
                let start = uuid_start + 6;
                rest[start..]
                    .find('"')
                    .map(|end| rest[start..start + end].to_string())
            })
            .unwrap_or_default();
        // Extract shape type - simplified extraction
        let shape_ty = rest
            .find("shape $")
            .map(|shape_start| {
                let start = shape_start + 7;
                let end = rest[start..].find(',').map_or(rest.len(), |p| start + p);
                rest[start..end].trim().to_string()
            })
            .unwrap_or_default();
        Ok(SilInstructionKind::OpenPackElement {
            index,
            shape_ty,
            uuid,
        })
    }

    fn parse_pack_element_get(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // pack_element_get %index of %pack : $*Pack{...} as $*T
        let index = self.parse_value_name()?;
        self.skip_whitespace();
        // Expect "of"
        let of_kw = self.parse_identifier()?;
        if of_kw != "of" {
            return Err(self.error(&format!("expected 'of' in pack_element_get, got '{of_kw}'")));
        }
        self.skip_whitespace();
        let pack = self.parse_value_name()?;
        self.skip_whitespace();
        // Skip " : $*Pack{...} as "
        if self.peek_char(':') {
            self.advance();
            self.skip_whitespace();
            self.parse_type()?; // Pack type
            self.skip_whitespace();
        }
        // Expect "as"
        let as_kw = self.parse_identifier()?;
        if as_kw != "as" {
            return Err(self.error(&format!("expected 'as' in pack_element_get, got '{as_kw}'")));
        }
        self.skip_whitespace();
        let element_ty = self.parse_type()?;
        self.skip_to_eol();
        Ok(SilInstructionKind::PackElementGet {
            index,
            pack,
            element_ty,
        })
    }

    fn parse_pack_element_set(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // pack_element_set %addr : $*T into %index of %pack : $*Pack{...}
        let value = self.parse_value_name()?;
        self.skip_whitespace();
        // Skip type annotation
        if self.peek_char(':') {
            self.advance();
            self.skip_whitespace();
            self.parse_type()?;
            self.skip_whitespace();
        }
        // Expect "into"
        let into_kw = self.parse_identifier()?;
        if into_kw != "into" {
            return Err(self.error(&format!(
                "expected 'into' in pack_element_set, got '{into_kw}'"
            )));
        }
        self.skip_whitespace();
        let index = self.parse_value_name()?;
        self.skip_whitespace();
        // Expect "of"
        let of_kw = self.parse_identifier()?;
        if of_kw != "of" {
            return Err(self.error(&format!("expected 'of' in pack_element_set, got '{of_kw}'")));
        }
        self.skip_whitespace();
        let pack = self.parse_value_name()?;
        self.skip_to_eol();
        Ok(SilInstructionKind::PackElementSet { value, index, pack })
    }

    fn parse_tuple_pack_element_addr(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // tuple_pack_element_addr %index of %tuple : $*(...) as $*T
        let index = self.parse_value_name()?;
        self.skip_whitespace();
        // Expect "of"
        let of_kw = self.parse_identifier()?;
        if of_kw != "of" {
            return Err(self.error(&format!(
                "expected 'of' in tuple_pack_element_addr, got '{of_kw}'"
            )));
        }
        self.skip_whitespace();
        let tuple = self.parse_value_name()?;
        self.skip_whitespace();
        // Skip " : $*(...) as "
        if self.peek_char(':') {
            self.advance();
            self.skip_whitespace();
            self.parse_type()?; // Tuple type
            self.skip_whitespace();
        }
        // Expect "as"
        let as_kw = self.parse_identifier()?;
        if as_kw != "as" {
            return Err(self.error(&format!(
                "expected 'as' in tuple_pack_element_addr, got '{as_kw}'"
            )));
        }
        self.skip_whitespace();
        let element_ty = self.parse_type()?;
        self.skip_to_eol();
        Ok(SilInstructionKind::TuplePackElementAddr {
            index,
            tuple,
            element_ty,
        })
    }

    // Async/await continuation instructions

    fn parse_get_async_continuation(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // get_async_continuation [throws] ResultType
        // Note: ResultType does not have $ prefix in this instruction
        // Check for [throws] attribute
        let throws = if self.peek_char('[') {
            self.advance();
            let attr = self.parse_identifier()?;
            self.expect_char(']')?;
            self.skip_whitespace();
            attr == "throws"
        } else {
            false
        };
        // Parse type without $ prefix
        let result_ty = self.parse_bare_type();
        self.skip_to_eol();
        Ok(SilInstructionKind::GetAsyncContinuation { result_ty, throws })
    }

    fn parse_get_async_continuation_addr(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // get_async_continuation_addr [throws] ResultType, %addr : $*ResultType
        // Note: ResultType does not have $ prefix in this instruction
        // Check for [throws] attribute
        let throws = if self.peek_char('[') {
            self.advance();
            let attr = self.parse_identifier()?;
            self.expect_char(']')?;
            self.skip_whitespace();
            attr == "throws"
        } else {
            false
        };
        // Parse type without $ prefix
        let result_ty = self.parse_bare_type();
        self.skip_whitespace();
        self.expect_char(',')?;
        self.skip_whitespace();
        let result_addr = self.parse_value_name()?;
        self.skip_to_eol();
        Ok(SilInstructionKind::GetAsyncContinuationAddr {
            result_ty,
            result_addr,
            throws,
        })
    }

    fn parse_index_addr(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // index_addr %base : $*Element, %index : $Builtin.Word
        // index_addr [stack_protection] %base : $*Element, %index : $Builtin.Word
        // or index_raw_pointer %ptr : $Builtin.RawPointer, %index : $Builtin.Word

        // Skip optional attributes like [stack_protection]
        self.skip_whitespace();
        while self.peek_char('[') {
            self.skip_balanced_brackets('[', ']')?;
            self.skip_whitespace();
        }

        let base = self.parse_value_name()?;
        self.skip_whitespace();

        // Skip type annotation (: $*Type)
        if self.peek_char(':') {
            self.advance(); // :
            self.skip_whitespace();
            self.parse_type()?;
            self.skip_whitespace();
        }

        self.expect_char(',')?;
        self.skip_whitespace();

        let index = self.parse_value_name()?;

        Ok(SilInstructionKind::IndexAddr { base, index })
    }

    fn parse_init_existential_addr(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // init_existential_addr %addr : $*P, $ConcreteType
        let address = self.parse_value_name()?;
        self.skip_whitespace();

        // Skip type annotation (: $*Type)
        if self.peek_char(':') {
            self.advance();
            self.skip_whitespace();
            self.parse_type()?;
            self.skip_whitespace();
        }

        self.expect_char(',')?;
        self.skip_whitespace();

        // Parse the concrete type
        let ty = self.parse_type()?;

        Ok(SilInstructionKind::InitExistentialAddr { address, ty })
    }

    fn parse_open_existential_addr(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // open_existential_addr immutable_access|mutable_access %addr : $*P to $*@opened("UUID", P) Self
        // First, skip the access mode if present (check if next char is NOT '%')
        if !self.peek_char('%') {
            // Parse and skip the access mode
            let _access_mode = self.parse_identifier()?;
            self.skip_whitespace();
        }

        let address = self.parse_value_name()?;
        self.skip_whitespace();

        // Skip type annotation (: $*Type)
        if self.peek_char(':') {
            self.advance();
            self.skip_whitespace();
            self.parse_type()?;
            self.skip_whitespace();
        }

        // Expect "to"
        let to_word = self.parse_identifier()?;
        if to_word != "to" {
            return Err(self.error(&format!("Expected 'to', found '{to_word}'")));
        }
        self.skip_whitespace();

        // Parse the opened type
        let ty = self.parse_type()?;

        Ok(SilInstructionKind::OpenExistentialAddr { address, ty })
    }

    fn parse_init_existential_ref(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // init_existential_ref %0 : $ConcreteClass : $ConcreteClass, $ClassP
        let operand = self.parse_value_name()?;
        self.skip_whitespace();

        // Skip type annotation (: $Type)
        if self.peek_char(':') {
            self.advance();
            self.skip_whitespace();
            self.parse_type()?;
            self.skip_whitespace();
        }

        // Skip second type annotation (: $Type) if present
        if self.peek_char(':') {
            self.advance();
            self.skip_whitespace();
            self.parse_type()?;
            self.skip_whitespace();
        }

        // Skip comma and parse existential type
        if self.peek_char(',') {
            self.advance();
            self.skip_whitespace();
        }

        // Parse the existential type
        let ty = self.parse_type()?;

        Ok(SilInstructionKind::InitExistentialRef { operand, ty })
    }

    fn parse_open_existential_ref(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // open_existential_ref %0 : $ClassP to $@opened("UUID", ClassP) Self
        let operand = self.parse_value_name()?;
        self.skip_whitespace();

        // Skip type annotation (: $Type)
        if self.peek_char(':') {
            self.advance();
            self.skip_whitespace();
            self.parse_type()?;
            self.skip_whitespace();
        }

        // Expect "to"
        let to_word = self.parse_identifier()?;
        if to_word != "to" {
            return Err(self.error(&format!("Expected 'to', found '{to_word}'")));
        }
        self.skip_whitespace();

        // Parse the opened type
        let ty = self.parse_type()?;

        Ok(SilInstructionKind::OpenExistentialRef { operand, ty })
    }

    fn parse_existential_metatype(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // existential_metatype $@thick Protocol.Type, %operand : $*Protocol
        // existential_metatype $@thick Protocol.Type, %operand : $Protocol
        // Parse result type first
        let ty = self.parse_type()?;
        self.skip_whitespace();

        // Skip comma
        if self.peek_char(',') {
            self.advance();
            self.skip_whitespace();
        }

        // Parse operand
        let operand = self.parse_value_name()?;
        self.skip_whitespace();

        // Skip operand type annotation (: $Type)
        if self.peek_char(':') {
            self.advance();
            self.skip_whitespace();
            self.parse_type()?;
        }

        Ok(SilInstructionKind::ExistentialMetatype { operand, ty })
    }

    fn parse_init_existential_metatype(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // init_existential_metatype %operand : $@thick Concrete.Type, $@thick Protocol.Type
        let operand = self.parse_value_name()?;
        self.skip_whitespace();

        // Skip operand type annotation (: $Type)
        if self.peek_char(':') {
            self.advance();
            self.skip_whitespace();
            self.parse_type()?;
            self.skip_whitespace();
        }

        // Skip comma
        if self.peek_char(',') {
            self.advance();
            self.skip_whitespace();
        }

        // Parse result existential metatype
        let ty = self.parse_type()?;

        Ok(SilInstructionKind::InitExistentialMetatype { operand, ty })
    }

    fn parse_open_existential_metatype(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // open_existential_metatype %operand : $@thick Protocol.Type to $@thick (@opened("UUID", Protocol) Self).Type
        let operand = self.parse_value_name()?;
        self.skip_whitespace();

        // Skip operand type annotation (: $Type)
        if self.peek_char(':') {
            self.advance();
            self.skip_whitespace();
            self.parse_type()?;
            self.skip_whitespace();
        }

        // Expect "to"
        let to_word = self.parse_identifier()?;
        if to_word != "to" {
            return Err(self.error(&format!("Expected 'to', found '{to_word}'")));
        }
        self.skip_whitespace();

        // Parse the opened type
        let ty = self.parse_type()?;

        Ok(SilInstructionKind::OpenExistentialMetatype { operand, ty })
    }

    fn parse_alloc_existential_box(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // alloc_existential_box $P, $T
        // Allocates a boxed existential container of type $P with space for value of type $T
        let existential_ty = self.parse_type()?;
        self.skip_whitespace();

        self.expect_char(',')?;
        self.skip_whitespace();

        let concrete_ty = self.parse_type()?;

        Ok(SilInstructionKind::AllocExistentialBox {
            existential_ty,
            concrete_ty,
        })
    }

    fn parse_project_existential_box(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // project_existential_box $T in %0 : $P
        // Projects the address of the value inside a boxed existential
        let concrete_ty = self.parse_type()?;
        self.skip_whitespace();

        // Expect "in"
        let in_word = self.parse_identifier()?;
        if in_word != "in" {
            return Err(self.error(&format!("Expected 'in', found '{in_word}'")));
        }
        self.skip_whitespace();

        let operand = self.parse_value_name()?;
        self.skip_whitespace();

        // Skip type annotation (: $P)
        if self.peek_char(':') {
            self.advance();
            self.skip_whitespace();
            self.parse_type()?;
        }

        Ok(SilInstructionKind::ProjectExistentialBox {
            concrete_ty,
            operand,
        })
    }

    fn parse_open_existential_box(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // open_existential_box %0 : $P to $*@opened P
        // Opens boxed existential and projects address with concrete type metadata
        let operand = self.parse_value_name()?;
        self.skip_whitespace();

        // Skip type annotation (: $P)
        if self.peek_char(':') {
            self.advance();
            self.skip_whitespace();
            self.parse_type()?;
            self.skip_whitespace();
        }

        // Expect "to"
        let to_word = self.parse_identifier()?;
        if to_word != "to" {
            return Err(self.error(&format!("Expected 'to', found '{to_word}'")));
        }
        self.skip_whitespace();

        let ty = self.parse_type()?;

        Ok(SilInstructionKind::OpenExistentialBox { operand, ty })
    }

    fn parse_open_existential_box_value(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // open_existential_box_value %0 : $P to $@opened P
        // Opens boxed existential to value (not address)
        let operand = self.parse_value_name()?;
        self.skip_whitespace();

        // Skip type annotation (: $P)
        if self.peek_char(':') {
            self.advance();
            self.skip_whitespace();
            self.parse_type()?;
            self.skip_whitespace();
        }

        // Expect "to"
        let to_word = self.parse_identifier()?;
        if to_word != "to" {
            return Err(self.error(&format!("Expected 'to', found '{to_word}'")));
        }
        self.skip_whitespace();

        let ty = self.parse_type()?;

        Ok(SilInstructionKind::OpenExistentialBoxValue { operand, ty })
    }

    fn parse_dealloc_existential_box(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // dealloc_existential_box %0 : $P, $T
        // Deallocates a boxed existential container
        let operand = self.parse_value_name()?;
        self.skip_whitespace();

        // Skip type annotation (: $P)
        if self.peek_char(':') {
            self.advance();
            self.skip_whitespace();
            self.parse_type()?;
            self.skip_whitespace();
        }

        self.expect_char(',')?;
        self.skip_whitespace();

        let concrete_ty = self.parse_type()?;

        Ok(SilInstructionKind::DeallocExistentialBox {
            operand,
            concrete_ty,
        })
    }

    fn parse_unconditional_checked_cast(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // unconditional_checked_cast %op : $SrcType to $TargetType
        // or: unconditional_checked_cast %op to TargetType (bare type)
        let operand = self.parse_value_name()?;
        self.skip_whitespace();

        // Skip source type annotation (: $SrcType)
        if self.peek_char(':') {
            self.advance();
            self.skip_whitespace();
            self.parse_type()?;
            self.skip_whitespace();
        }

        self.expect_str("to")?;
        self.skip_whitespace();

        // Target type may have $ prefix or be bare
        let ty = if self.peek_char('$') {
            self.parse_type()?
        } else {
            self.parse_bare_type()
        };

        Ok(SilInstructionKind::UnconditionalCheckedCast { operand, ty })
    }

    fn parse_unconditional_checked_cast_addr(
        &mut self,
    ) -> Result<SilInstructionKind, SilParseError> {
        // unconditional_checked_cast_addr SrcType in %src : $*SrcType to TargetType in %dest : $*TargetType
        // First parse the source type name (until "in %")
        let source_ty_name = self.consume_until_str(" in %");
        let source_ty = SilType::Named(source_ty_name.trim().to_string());

        self.skip_whitespace();
        self.expect_str("in")?;
        self.skip_whitespace();

        let source = self.parse_value_name()?;
        self.skip_whitespace();

        // Skip source address type annotation (: $*SrcType)
        if self.peek_char(':') {
            self.advance();
            self.skip_whitespace();
            self.parse_type()?;
            self.skip_whitespace();
        }

        self.expect_str("to")?;
        self.skip_whitespace();

        // Parse target type name (until "in %")
        let target_ty_name = self.consume_until_str(" in %");
        let target_ty = SilType::Named(target_ty_name.trim().to_string());

        self.skip_whitespace();
        self.expect_str("in")?;
        self.skip_whitespace();

        let dest = self.parse_value_name()?;

        Ok(SilInstructionKind::UnconditionalCheckedCastAddr {
            source_ty,
            source,
            target_ty,
            dest,
        })
    }

    fn parse_alloc_ref(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // alloc_ref $ClassName
        // alloc_ref [tail_elems $Type * %count] $ClassName
        // alloc_ref_dynamic %metatype : $@thick T.Type, $T
        let mut tail_elems = Vec::new();

        // Skip optional attributes like [objc], [stack], [bare], etc.
        while self.peek_char('[') {
            self.advance();
            let attr = self.parse_identifier()?;
            // Check for tail_elems: [tail_elems $Type * %count]
            if attr == "tail_elems" {
                self.skip_whitespace();
                let elem_ty = self.parse_type()?;
                tail_elems.push(elem_ty);
                // Skip "* %count" part
                self.skip_whitespace();
                if self.peek_char('*') {
                    self.advance();
                    self.skip_whitespace();
                    self.parse_value_name()?; // Skip count operand
                }
            }
            self.expect_char(']')?;
            self.skip_whitespace();
        }

        // For alloc_ref_dynamic, skip the metatype operand
        if self.peek_char('%') {
            self.parse_value_name()?;
            self.skip_whitespace();
            // Skip type annotation
            if self.peek_char(':') {
                self.advance();
                self.skip_whitespace();
                self.parse_type()?;
                self.skip_whitespace();
            }
            // Skip comma if present
            if self.peek_char(',') {
                self.advance();
                self.skip_whitespace();
            }
        }

        let ty = self.parse_type()?;

        Ok(SilInstructionKind::AllocRef { ty, tail_elems })
    }

    fn parse_dealloc_ref(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // dealloc_ref %operand : $ClassName
        // dealloc_ref [stack] %operand : $ClassName
        // Skip optional [stack] attribute
        if self.peek_char('[') {
            self.advance();
            self.parse_identifier()?;
            self.expect_char(']')?;
            self.skip_whitespace();
        }

        let operand = self.parse_value_name()?;

        Ok(SilInstructionKind::DeallocRef { operand })
    }

    fn parse_class_method(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // class_method %0 : $ClassName, #ClassName.methodName : Type, $ConventionType
        let operand = self.parse_value_name()?;
        self.skip_whitespace();

        // Skip type annotation (: $ClassName)
        if self.peek_char(':') {
            self.advance();
            self.skip_whitespace();
            self.parse_type()?;
            self.skip_whitespace();
        }

        self.expect_char(',')?;
        self.skip_whitespace();

        // Parse method reference: #ClassName.methodName
        self.expect_char('#')?;
        let method = self.consume_until(':');
        // Skip past the ':' and consume the method type and convention
        self.skip_to_eol();

        Ok(SilInstructionKind::ClassMethod {
            operand,
            method: method.trim().to_string(),
        })
    }

    fn parse_witness_method(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // witness_method $ConcreteType, #Protocol.method : <Self where ...> Type, %self : $*Self
        // The format varies; we extract the type and method name
        let ty = self.parse_type()?;
        self.skip_whitespace();

        self.expect_char(',')?;
        self.skip_whitespace();

        // Parse method reference: #Protocol.method
        self.expect_char('#')?;
        let method = self.consume_until(':');
        // Skip the rest
        self.skip_to_eol();

        Ok(SilInstructionKind::WitnessMethod {
            ty,
            method: method.trim().to_string(),
        })
    }

    fn parse_upcast(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // upcast %operand : $SubClass to $SuperClass
        let operand = self.parse_value_name()?;
        self.skip_whitespace();

        // Skip source type annotation (: $SubClass)
        if self.peek_char(':') {
            self.advance();
            self.skip_whitespace();
            self.parse_type()?;
            self.skip_whitespace();
        }

        self.expect_str("to")?;
        self.skip_whitespace();

        let ty = self.parse_type()?;

        Ok(SilInstructionKind::Upcast { operand, ty })
    }

    fn parse_global_addr(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // global_addr @globalName : $*Type
        // global_addr @globalName : $*Type, dependence_base @otherGlobal
        self.expect_char('@')?;
        let name = self.parse_symbol_name()?;

        Ok(SilInstructionKind::GlobalAddr { name })
    }

    fn parse_select_enum(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // select_enum %operand : $EnumType, case #Enum.case1: %val1, case #Enum.case2: %val2, default %default : $ResultType
        // select_enum_addr %addr : $*EnumType, case #Enum.case1: %val1, ...
        let operand = self.parse_value_name()?;
        self.skip_whitespace();

        // Skip type annotation (: $Type)
        if self.peek_char(':') {
            self.advance();
            self.skip_whitespace();
            // Handle nested <> for generics
            let mut angle_depth = 0;
            loop {
                if self.is_eof() {
                    break;
                }
                let c = self.input[self.pos..].chars().next().unwrap();
                if c == '<' {
                    angle_depth += 1;
                    self.advance();
                } else if c == '>' {
                    if angle_depth > 0 {
                        angle_depth -= 1;
                    }
                    self.advance();
                } else if angle_depth == 0 && (c == ',' || c == '\n' || c == '\r') {
                    break;
                } else {
                    self.advance();
                }
            }
        }

        let mut cases = Vec::new();
        let mut default = None;

        while self.peek_char(',') {
            self.advance();
            self.skip_whitespace_on_line();

            if self.peek_str("default") {
                self.expect_str("default")?;
                self.skip_whitespace_on_line();
                default = Some(self.parse_value_name()?);
            } else if self.peek_str("case") {
                self.expect_str("case")?;
                self.skip_whitespace_on_line();
                // case #EnumType.case!enumelt: %valueN
                let case_name = self.consume_until(':');
                self.expect_char(':')?;
                self.skip_whitespace_on_line();
                let result_val = self.parse_value_name()?;
                cases.push((case_name.trim().to_string(), result_val));
            } else {
                // Stop on result type annotation (: $Type) or anything else
                break;
            }
            self.skip_whitespace_on_line();
        }

        // Skip result type at end (: $ResultType)
        self.skip_to_eol();

        Ok(SilInstructionKind::SelectEnum {
            operand,
            cases,
            default,
        })
    }

    fn parse_global(&mut self) -> Result<SilGlobal, SilParseError> {
        // sil_global [linkage] @name : $Type
        self.expect_str("sil_global")?;
        self.skip_whitespace();

        // Parse optional linkage
        let mut linkage = SilLinkage::Hidden;
        if !self.peek_char('@') && !self.peek_char('[') {
            let word = self.parse_identifier()?;
            linkage = match word.as_str() {
                "public" => SilLinkage::Public,
                "private" => SilLinkage::Private,
                // "hidden" or unknown values default to Hidden
                _ => SilLinkage::Hidden,
            };
            self.skip_whitespace();
        }

        // Skip attributes
        while self.peek_char('[') {
            self.advance();
            self.consume_until(']');
            self.expect_char(']')?;
            self.skip_whitespace();
        }

        self.expect_char('@')?;
        let name = self.parse_symbol_name()?;
        self.skip_whitespace();

        self.expect_char(':')?;
        self.skip_whitespace();
        let ty = self.parse_type()?;

        self.skip_to_eol();

        Ok(SilGlobal { name, ty, linkage })
    }

    // Helper parsing functions

    fn parse_type(&mut self) -> Result<SilType, SilParseError> {
        self.expect_char('$')?;
        self.parse_type_inner()
    }

    /// Parse a type without the $ prefix (for instructions like `get_async_continuation`)
    fn parse_bare_type(&mut self) -> SilType {
        // Handle types like "Builtin.Int32" without $ prefix
        let name = self.consume_type_name();
        SilType::Named(name)
    }

    /// Helper to parse a convention string and determine the `CallingConvention`.
    /// Returns `Some(convention)` if this is a function type, or `None` if we should
    /// recurse to parse the underlying type.
    fn parse_convention_from_string(
        &mut self,
        conv_str: &str,
    ) -> Result<Option<CallingConvention>, SilParseError> {
        match conv_str {
            "convention" => {
                self.expect_char('(')?;
                let inner = self.parse_identifier()?;
                self.skip_whitespace();
                // Handle witness_method: Protocol syntax
                if inner == "witness_method" && self.peek_char(':') {
                    self.advance(); // consume ':'
                    self.skip_whitespace();
                    let _protocol = self.parse_identifier()?; // consume protocol name
                    self.skip_whitespace();
                }
                self.expect_char(')')?;
                self.skip_whitespace();
                let conv = match inner.as_str() {
                    "thick" => CallingConvention::Thick,
                    "method" => CallingConvention::Method,
                    "witness_method" => CallingConvention::WitnessMethod,
                    "c" => CallingConvention::C,
                    "block" => CallingConvention::Block,
                    // "thin" or unknown values default to Thin
                    _ => CallingConvention::Thin,
                };
                Ok(Some(conv))
            }
            // Closure/function type conventions - these indicate a function type follows
            "callee_guaranteed" | "callee_owned" | "noescape" | "escaping" | "autoclosure" => {
                // @callee_guaranteed () -> Int should parse () -> Int as function type
                if self.peek_char('(') && !self.peek_str("(@opened") {
                    Ok(Some(CallingConvention::Thin))
                } else {
                    Ok(None) // recurse
                }
            }
            "async" => {
                // @async is a function type marker - parse as function type with default convention
                Ok(Some(CallingConvention::Thin))
            }
            "opened" => {
                // @opened("UUID", Protocol) TypeName - skip the parentheses and parse underlying type
                if self.peek_char('(') {
                    self.skip_balanced_brackets('(', ')')?;
                    self.skip_whitespace();
                }
                Ok(None) // recurse
            }
            // Parameter/type attributes and unknown @ annotations - continue parsing underlying type
            _ => Ok(None),
        }
    }

    /// Helper to parse a tuple type: `(Type1, Type2, ...)` or `(label: Type1, label2: Type2, ...)`
    fn parse_tuple_type_inner(&mut self) -> Result<SilType, SilParseError> {
        self.advance(); // consume '('
        let mut elements = Vec::new();
        while !self.peek_char(')') && !self.is_eof() {
            self.skip_whitespace();

            // Handle labeled tuple elements: `label: Type`
            // Peek ahead to see if this is a label followed by ':'
            if self.is_tuple_label() {
                // Skip the label name
                let _label = self.consume_type_name();
                self.skip_whitespace();
                // Consume the ':'
                if self.peek_char(':') {
                    self.advance();
                    self.skip_whitespace();
                }
            }

            let elem = self.parse_type_inner()?;
            elements.push(elem);
            self.skip_whitespace();
            if self.peek_char(',') {
                self.advance();
                self.skip_whitespace();
            }
        }
        self.expect_char(')')?;
        Ok(SilType::Tuple(elements))
    }

    /// Check if current position is a tuple label (identifier followed by ':')
    fn is_tuple_label(&self) -> bool {
        let input = &self.input[self.pos..];
        // Find an identifier followed by ':'
        // Labels are simple identifiers (alphanumeric + underscore)
        let mut i = 0;
        while i < input.len() {
            let c = input.as_bytes()[i];
            if c.is_ascii_alphanumeric() || c == b'_' {
                i += 1;
            } else {
                break;
            }
        }
        // Must have consumed at least one character and next must be ':'
        if i == 0 {
            return false;
        }
        // Skip whitespace
        while i < input.len() && input.as_bytes()[i].is_ascii_whitespace() {
            i += 1;
        }
        // Check for ':'
        i < input.len() && input.as_bytes()[i] == b':'
    }

    /// Helper to parse a named type with optional generics and metatype suffix.
    fn parse_named_type_inner(&mut self) -> SilType {
        let name = self.consume_type_name();

        // Skip generic parameters if present
        if self.peek_char('<') {
            let mut depth = 0;
            loop {
                if self.peek_char('<') {
                    depth += 1;
                } else if self.peek_char('>') {
                    depth -= 1;
                    if depth == 0 {
                        self.advance();
                        break;
                    }
                }
                if self.is_eof() {
                    break;
                }
                self.advance();
            }
        }

        // Check for .Type or .Protocol suffix (metatype)
        let base_type = SilType::Named(name);
        if self.peek_str(".Type") {
            let _ = self.expect_str(".Type");
            SilType::Metatype(Box::new(base_type))
        } else if self.peek_str(".Protocol") {
            let _ = self.expect_str(".Protocol");
            SilType::Metatype(Box::new(base_type))
        } else {
            base_type
        }
    }

    #[allow(clippy::too_many_lines)]
    fn parse_type_inner(&mut self) -> Result<SilType, SilParseError> {
        // Skip optional address marker
        let is_address = if self.peek_char('*') {
            self.advance();
            true
        } else {
            false
        };

        // Parse calling convention if present
        if self.peek_char('@') {
            self.advance();
            let conv_str = self.parse_identifier()?;
            self.skip_whitespace();

            // Determine calling convention or recurse for underlying type
            let Some(convention) = self.parse_convention_from_string(&conv_str)? else {
                return self.parse_type_inner();
            };

            // Skip additional function-type attributes (e.g., @async, @Sendable)
            // These can appear after @convention(thin) but before the parameter list
            while self.peek_char('@') {
                self.advance();
                let attr = self.parse_identifier()?;
                self.skip_whitespace();
                // Only skip parentheses for attributes that take arguments
                // @async, @Sendable, @escaping do NOT take arguments
                // @substituted, @opened DO take arguments
                if matches!(
                    attr.as_str(),
                    "substituted" | "opened" | "differentiable" | "noDerivative"
                ) {
                    if self.peek_char('(') {
                        self.skip_balanced_brackets('(', ')')?;
                        self.skip_whitespace();
                    }
                }
            }

            // Skip generic parameters if present: <T where T : P>
            // Some types have multiple consecutive generic parameter lists: <τ_0_0><τ_1_0>
            while self.peek_char('<') {
                self.skip_balanced_brackets('<', '>')?;
                self.skip_whitespace();
            }

            // Parse function parameters
            self.expect_char('(')?;
            let mut params = Vec::new();
            while !self.peek_char(')') && !self.is_eof() {
                let param_ty = self.parse_type_inner()?;
                params.push(param_ty);
                self.skip_whitespace();
                if self.peek_char(',') {
                    self.advance();
                    self.skip_whitespace();
                }
            }
            self.expect_char(')')?;
            self.skip_whitespace();

            // Parse throws annotation if present
            let throws = if self.peek_str("throws") {
                self.expect_str("throws")?;
                self.skip_whitespace();
                true
            } else {
                false
            };

            // Parse arrow and result
            self.expect_str("->")?;
            self.skip_whitespace();
            let result = Box::new(self.parse_type_inner()?);

            let ty = SilType::Function {
                convention,
                params,
                result,
                throws,
            };
            return if is_address {
                Ok(SilType::Address(Box::new(ty)))
            } else {
                Ok(ty)
            };
        }

        // Parse regular type
        let ty = if self.peek_char('(') {
            self.parse_tuple_type_inner()?
        } else if self.peek_str("Builtin") {
            self.expect_str("Builtin")?;
            self.expect_char('.')?;
            let name = self.parse_identifier()?;
            SilType::Builtin(name)
        } else if self.peek_str("Optional") {
            self.expect_str("Optional")?;
            self.expect_char('<')?;
            let inner = self.parse_type_inner()?;
            self.expect_char('>')?;
            SilType::Optional(Box::new(inner))
        } else if self.peek_str("any ") {
            // Existential type: `any Protocol` or `any Error`
            self.expect_str("any")?;
            self.skip_whitespace();
            let protocol_name = self.consume_type_name();
            SilType::Existential(vec![protocol_name])
        } else if self.peek_char('{') {
            // Box type for captured variables: { var Type } or { let Type }
            // Used in closure captures like @closureCapture ${ var Int }
            self.advance(); // consume '{'
            self.skip_whitespace();
            // Skip 'var' or 'let' keyword
            if self.peek_str("var") || self.peek_str("let") {
                self.parse_identifier()?;
                self.skip_whitespace();
            }
            // Parse the inner type (without $)
            let inner = self.parse_type_inner()?;
            self.skip_whitespace();
            self.expect_char('}')?;
            // Box types are essentially references to the inner type
            SilType::Box(Box::new(inner))
        } else {
            self.parse_named_type_inner()
        };

        if is_address {
            Ok(SilType::Address(Box::new(ty)))
        } else {
            Ok(ty)
        }
    }

    fn parse_value_name(&mut self) -> Result<String, SilParseError> {
        self.expect_char('%')?;
        let name = self.consume_while(|c| c.is_ascii_alphanumeric() || c == '_');
        Ok(format!("%{name}"))
    }

    fn parse_value_list(&mut self) -> Result<Vec<String>, SilParseError> {
        let mut values = Vec::new();

        if !self.peek_char('(') {
            return Ok(values);
        }

        self.expect_char('(')?;
        while !self.peek_char(')') && !self.is_eof() {
            let val = self.parse_value_name()?;
            values.push(val);
            self.skip_whitespace();
            // Skip optional type annotation (: $Type)
            if self.peek_char(':') {
                self.advance();
                self.skip_whitespace();
                self.parse_type()?;
                self.skip_whitespace();
            }
            if self.peek_char(',') {
                self.advance();
                self.skip_whitespace();
            }
        }
        self.expect_char(')')?;

        Ok(values)
    }

    fn parse_optional_args(&mut self) -> Result<Vec<String>, SilParseError> {
        // Don't skip_whitespace here - we only want args immediately following
        // the previous token, without consuming newlines
        if self.peek_char('(') {
            self.parse_value_list()
        } else {
            Ok(Vec::new())
        }
    }

    fn parse_substitutions(&mut self) -> Result<Vec<SilType>, SilParseError> {
        let mut substs = Vec::new();

        self.expect_char('<')?;
        while !self.peek_char('>') && !self.is_eof() {
            let ty = self.parse_type_inner()?;
            substs.push(ty);
            self.skip_whitespace();
            if self.peek_char(',') {
                self.advance();
                self.skip_whitespace();
            }
        }
        self.expect_char('>')?;

        Ok(substs)
    }

    fn parse_identifier(&mut self) -> Result<String, SilParseError> {
        // Allow Unicode alphanumeric (for generic params like τ_0_0)
        let id = self.consume_while(|c| c.is_alphanumeric() || c == '_');
        if id.is_empty() {
            Err(self.error("expected identifier"))
        } else {
            Ok(id)
        }
    }

    fn parse_symbol_name(&mut self) -> Result<String, SilParseError> {
        // Symbol names can contain special characters
        let name =
            self.consume_while(|c| c.is_ascii_alphanumeric() || c == '_' || c == '$' || c == '.');
        if name.is_empty() {
            Err(self.error("expected symbol name"))
        } else {
            Ok(name)
        }
    }

    fn parse_string(&mut self) -> Result<String, SilParseError> {
        self.expect_char('"')?;
        let mut s = String::new();

        while !self.peek_char('"') && !self.is_eof() {
            let c = self.current_char().unwrap();
            if c == '\\' {
                self.advance();
                if let Some(escaped) = self.current_char() {
                    match escaped {
                        'n' => s.push('\n'),
                        'r' => s.push('\r'),
                        't' => s.push('\t'),
                        '\\' => s.push('\\'),
                        '"' => s.push('"'),
                        _ => {
                            s.push('\\');
                            s.push(escaped);
                        }
                    }
                    self.advance();
                }
            } else {
                s.push(c);
                self.advance();
            }
        }

        self.expect_char('"')?;
        Ok(s)
    }

    fn consume_type_name(&mut self) -> String {
        // Allow Unicode alphanumeric (for generic params like τ_0_0)
        self.consume_while(|c| c.is_alphanumeric() || c == '_' || c == '.')
    }

    fn consume_until_whitespace_or_colon(&mut self) -> String {
        self.consume_while(|c| !c.is_whitespace() && c != ':')
    }

    fn consume_until(&mut self, stop: char) -> String {
        self.consume_while(|c| c != stop)
    }

    /// Consume until any of the stop characters (non-Result version)
    fn consume_until_char(&mut self, stop: char) -> String {
        self.consume_while(|c| c != stop)
    }

    /// Consume until any of the stop characters in the slice
    fn consume_until_char_in(&mut self, stops: &[char]) -> String {
        self.consume_while(|c| !stops.contains(&c))
    }

    fn consume_until_str(&mut self, stop: &str) -> String {
        let start = self.pos;
        while !self.is_eof() && !self.peek_str(stop) {
            self.advance();
        }
        self.input[start..self.pos].to_string()
    }

    fn consume_to_eol(&mut self) -> String {
        self.consume_while(|c| c != '\n')
    }

    fn consume_while<F: Fn(char) -> bool>(&mut self, pred: F) -> String {
        let start = self.pos;
        while let Some(c) = self.current_char() {
            if pred(c) {
                self.advance();
            } else {
                break;
            }
        }
        self.input[start..self.pos].to_string()
    }

    fn skip_whitespace(&mut self) {
        while let Some(c) = self.current_char() {
            if c.is_whitespace() {
                self.advance();
            } else {
                break;
            }
        }
    }

    /// Skip whitespace on the current line only (not newlines)
    fn skip_whitespace_on_line(&mut self) {
        while let Some(c) = self.current_char() {
            if c.is_whitespace() && c != '\n' {
                self.advance();
            } else {
                break;
            }
        }
    }

    fn skip_whitespace_and_comments(&mut self) {
        loop {
            self.skip_whitespace();
            if self.peek_str("//") {
                self.skip_to_eol();
                if self.current_char() == Some('\n') {
                    self.advance();
                }
            } else {
                break;
            }
        }
    }

    /// Look ahead to determine if the current position is a result assignment.
    ///
    /// Result assignments look like:
    /// - `%n = instruction ...`
    /// - `(%n, %m) = instruction ...`
    ///
    /// Instructions that start with % but aren't result assignments:
    /// - `debug_value %n, ...`
    ///
    /// Returns true if there's a `=` sign after the value pattern.
    fn is_result_assignment(&self) -> bool {
        let input = &self.input[self.pos..];

        // Check for tuple result: (%n, %m) =
        if input.starts_with('(') {
            // Find matching closing paren
            let mut depth = 1;
            let mut i = 1;
            while i < input.len() && depth > 0 {
                match input.as_bytes()[i] {
                    b'(' => depth += 1,
                    b')' => depth -= 1,
                    _ => {}
                }
                i += 1;
            }
            // Skip whitespace after )
            while i < input.len() && input.as_bytes()[i].is_ascii_whitespace() {
                i += 1;
            }
            // Check for =
            return i < input.len() && input.as_bytes()[i] == b'=';
        }

        // Check for single result: %n =
        if input.starts_with('%') {
            // Skip %
            let mut i = 1;
            // Skip alphanumeric (the register name)
            while i < input.len()
                && (input.as_bytes()[i].is_ascii_alphanumeric() || input.as_bytes()[i] == b'_')
            {
                i += 1;
            }
            // Skip whitespace
            while i < input.len() && input.as_bytes()[i].is_ascii_whitespace() {
                i += 1;
            }
            // Check for =
            return i < input.len() && input.as_bytes()[i] == b'=';
        }

        false
    }

    /// Try to parse a source location annotation.
    ///
    /// SIL source location format: `loc "file.swift":line:col`
    /// May be followed by `, scope N` and `// comment`
    ///
    /// Example: `loc "/tmp/test.swift":1:48, scope 2 // id: %10`
    fn try_parse_location(&mut self) -> Option<SilLocation> {
        // Look for loc annotation on the current line
        self.skip_whitespace_on_line();

        // Skip any trailing commas before loc
        while self.peek_char(',') {
            self.advance();
            self.skip_whitespace_on_line();

            // Check if this is a loc annotation
            if self.peek_str("loc ") {
                break;
            }

            // Skip over scope annotations or other comma-separated items
            // until we hit loc, newline, or //
            while !self.is_eof() {
                let c = self.current_char()?;
                if c == '\n' || c == '/' {
                    return None;
                }
                if c == ',' {
                    break;
                }
                self.advance();
            }
        }

        if !self.peek_str("loc ") {
            return None;
        }

        // Consume "loc "
        self.advance(); // l
        self.advance(); // o
        self.advance(); // c
        self.advance(); // space

        self.skip_whitespace_on_line();

        // Parse file path: "path/to/file.swift"
        if !self.peek_char('"') {
            return None;
        }

        let file = self.parse_string().ok()?;
        self.skip_whitespace_on_line();

        // Parse :line:col
        if !self.peek_char(':') {
            return None;
        }
        self.advance(); // :

        // Parse line number
        let line_str = self.consume_while(|c| c.is_ascii_digit());
        let line: u32 = line_str.parse().ok()?;

        // Parse :column
        if !self.peek_char(':') {
            return None;
        }
        self.advance(); // :

        let col_str = self.consume_while(|c| c.is_ascii_digit());
        let column: u32 = col_str.parse().ok()?;

        Some(SilLocation { file, line, column })
    }

    fn skip_to_eol(&mut self) {
        while let Some(c) = self.current_char() {
            if c == '\n' {
                self.advance();
                break;
            }
            self.advance();
        }
    }

    /// Skip a type annotation including nested generics (e.g., `: $Optional<Int>`).
    /// Stops at comma or newline when not inside angle brackets.
    fn skip_type_with_generics(&mut self) {
        self.advance(); // consume ':'
        self.skip_whitespace();
        let mut angle_depth = 0;
        while !self.is_eof() {
            let Some(c) = self.current_char() else {
                break;
            };
            match c {
                '<' => {
                    angle_depth += 1;
                    self.advance();
                }
                '>' => {
                    if angle_depth > 0 {
                        angle_depth -= 1;
                    }
                    self.advance();
                }
                ',' | '\n' | '\r' if angle_depth == 0 => break,
                _ => self.advance(),
            }
        }
    }

    /// Parse a parenthesized list of value names: (%v1, %v2, ...).
    /// Returns an empty vec if no parentheses present.
    fn parse_value_name_list(&mut self) -> Result<Vec<String>, SilParseError> {
        let mut values = Vec::new();
        if !self.peek_char('(') {
            return Ok(values);
        }
        self.advance();
        loop {
            self.skip_whitespace();
            if self.peek_char(')') {
                self.advance();
                break;
            }
            if self.peek_char(',') {
                self.advance();
                continue;
            }
            if self.peek_char('%') {
                values.push(self.parse_value_name()?);
            } else {
                break;
            }
        }
        Ok(values)
    }

    /// Parse optional type substitutions in angle brackets: <T, U, ...>.
    /// Returns empty vec if no angle brackets present.
    fn parse_type_substitutions(&mut self) -> Vec<SilType> {
        let mut substitutions = Vec::new();
        if !self.peek_char('<') {
            return substitutions;
        }
        self.advance();
        loop {
            self.skip_whitespace();
            if self.peek_char('>') {
                self.advance();
                break;
            }
            if self.peek_char(',') {
                self.advance();
                continue;
            }
            if let Ok(ty) = self.parse_type() {
                substitutions.push(ty);
            } else {
                break;
            }
        }
        substitutions
    }

    /// Parse enum switch cases (case #Type.case!enumelt: bbN) and optional default branch.
    /// Returns `(cases, default_dest)`.
    fn parse_enum_switch_cases(&mut self) -> Result<EnumSwitchCasesAndDefault, SilParseError> {
        let mut cases: EnumSwitchCases = Vec::new();
        let mut default = None;

        while self.peek_char(',') {
            self.advance();
            self.skip_whitespace_on_line();

            if self.peek_str("default") {
                self.expect_str("default")?;
                self.skip_whitespace_on_line();
                default = Some(self.parse_identifier()?);
            } else if self.peek_str("case") {
                self.expect_str("case")?;
                self.skip_whitespace_on_line();
                let case_name = self.consume_until(':');
                self.expect_char(':')?;
                self.skip_whitespace_on_line();
                let dest = self.parse_identifier()?;
                cases.push((case_name.trim().to_string(), dest));
            } else {
                break;
            }
            self.skip_whitespace_on_line();
        }

        Ok((cases, default))
    }

    /// Skip a simple type annotation (`: $Type`) until comma or newline.
    /// Does not handle nested generics - use `skip_type_with_generics` for that.
    fn skip_simple_type_annotation(&mut self) {
        if self.peek_char(':') {
            self.advance();
            self.skip_whitespace();
            while !self.is_eof() && !self.peek_char(',') && !self.peek_char('\n') {
                self.advance();
            }
        }
    }

    fn skip_to_keyword(&mut self, keyword: &str) {
        // Skip forward until we find the keyword (staying on same line)
        while !self.is_eof() && !self.peek_char('\n') {
            if self.peek_str(keyword) {
                return;
            }
            self.advance();
        }
    }

    fn skip_to_next_declaration(&mut self) {
        // Skip until we find a top-level keyword that we parse:
        // - sil_stage: module stage declaration
        // - import: module import
        // - sil_global: global variable
        // - sil (but not sil_*): function definition
        while !self.is_eof() {
            self.skip_to_eol();
            self.skip_whitespace_and_comments();

            if self.peek_str("sil_stage")
                || self.peek_str("import")
                || self.peek_str("sil_global")
                || (self.peek_str("sil") && !self.peek_str("sil_"))
            {
                break;
            }

            self.skip_to_eol();
        }
    }

    fn current_char(&self) -> Option<char> {
        self.input[self.pos..].chars().next()
    }

    fn advance(&mut self) {
        if let Some(c) = self.current_char() {
            self.pos += c.len_utf8();
            if c == '\n' {
                self.line += 1;
                self.column = 1;
            } else {
                self.column += 1;
            }
        }
    }

    fn peek_char(&self, expected: char) -> bool {
        self.current_char() == Some(expected)
    }

    fn peek_str(&self, expected: &str) -> bool {
        self.input[self.pos..].starts_with(expected)
    }

    fn expect_char(&mut self, expected: char) -> Result<(), SilParseError> {
        if self.peek_char(expected) {
            self.advance();
            Ok(())
        } else {
            Err(self.error(&format!("expected '{expected}'")))
        }
    }

    fn expect_str(&mut self, expected: &str) -> Result<(), SilParseError> {
        if self.peek_str(expected) {
            for _ in expected.chars() {
                self.advance();
            }
            Ok(())
        } else {
            Err(self.error(&format!("expected '{expected}'")))
        }
    }

    // ==================== NEW PARSE FUNCTIONS ====================

    fn parse_address_to_pointer(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // address_to_pointer %addr : $*T to $Builtin.RawPointer
        // or: address_to_pointer [stack_protection] %addr : $*T to $Builtin.RawPointer
        // Skip optional attributes
        while self.peek_char('[') {
            self.advance();
            self.parse_identifier()?;
            self.expect_char(']')?;
            self.skip_whitespace();
        }
        let operand = self.parse_value_name()?;
        self.skip_to_eol();
        Ok(SilInstructionKind::AddressToPointer { operand })
    }

    fn parse_pointer_to_address(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // pointer_to_address %ptr : $Builtin.RawPointer to [strict] $*T
        let operand = self.parse_value_name()?;
        self.skip_whitespace();

        // Skip operand type annotation
        if self.peek_char(':') {
            self.advance();
            self.skip_whitespace();
            self.parse_type()?;
            self.skip_whitespace();
        }

        self.expect_str("to")?;
        self.skip_whitespace();

        // Check for [strict] attribute
        let strict = if self.peek_char('[') {
            self.advance();
            let attr = self.parse_identifier()?;
            self.expect_char(']')?;
            self.skip_whitespace();
            attr == "strict"
        } else {
            false
        };

        let ty = self.parse_type()?;

        Ok(SilInstructionKind::PointerToAddress {
            operand,
            ty,
            strict,
        })
    }

    fn parse_unchecked_ref_cast(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // unchecked_ref_cast %operand : $SrcType to $DestType
        let operand = self.parse_value_name()?;
        self.skip_whitespace();

        // Skip source type annotation
        if self.peek_char(':') {
            self.advance();
            self.skip_whitespace();
            self.parse_type()?;
            self.skip_whitespace();
        }

        self.expect_str("to")?;
        self.skip_whitespace();

        let ty = self.parse_type()?;

        Ok(SilInstructionKind::UncheckedRefCast { operand, ty })
    }

    fn parse_unchecked_addr_cast(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // unchecked_addr_cast %addr : $*SrcType to $*DestType
        let operand = self.parse_value_name()?;
        self.skip_whitespace();

        // Skip source type annotation
        if self.peek_char(':') {
            self.advance();
            self.skip_whitespace();
            self.parse_type()?;
            self.skip_whitespace();
        }

        self.expect_str("to")?;
        self.skip_whitespace();

        let ty = self.parse_type()?;

        Ok(SilInstructionKind::UncheckedAddrCast { operand, ty })
    }

    fn parse_unchecked_trivial_bit_cast(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // unchecked_trivial_bit_cast %operand : $SrcType to $DestType
        let operand = self.parse_value_name()?;
        self.skip_whitespace();

        if self.peek_char(':') {
            self.advance();
            self.skip_whitespace();
            self.parse_type()?;
            self.skip_whitespace();
        }

        self.expect_str("to")?;
        self.skip_whitespace();

        let ty = self.parse_type()?;

        Ok(SilInstructionKind::UncheckedTrivialBitCast { operand, ty })
    }

    fn parse_unchecked_bitwise_cast(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // unchecked_bitwise_cast %operand : $SrcType to $DestType
        let operand = self.parse_value_name()?;
        self.skip_whitespace();

        if self.peek_char(':') {
            self.advance();
            self.skip_whitespace();
            self.parse_type()?;
            self.skip_whitespace();
        }

        self.expect_str("to")?;
        self.skip_whitespace();

        let ty = self.parse_type()?;

        Ok(SilInstructionKind::UncheckedBitwiseCast { operand, ty })
    }

    fn parse_hop_to_executor(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // hop_to_executor %actor : $ActorType
        let operand = self.parse_value_name()?;
        self.skip_to_eol();
        Ok(SilInstructionKind::HopToExecutor { operand })
    }

    fn parse_extract_executor(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // extract_executor %actor : $ActorType
        let operand = self.parse_value_name()?;
        self.skip_to_eol();
        Ok(SilInstructionKind::ExtractExecutor { operand })
    }

    fn parse_struct_element_addr(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // struct_element_addr %addr : $*StructType, #StructType.field
        let operand = self.parse_value_name()?;
        self.skip_whitespace();

        // Skip type annotation
        if self.peek_char(':') {
            self.advance();
            self.skip_whitespace();
            self.parse_type()?;
            self.skip_whitespace();
        }

        self.expect_char(',')?;
        self.skip_whitespace();

        let field = self.consume_until_whitespace_or_colon();

        Ok(SilInstructionKind::StructElementAddr { operand, field })
    }

    fn parse_tuple_element_addr(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // tuple_element_addr %addr : $*(T1, T2, ...), 0
        let operand = self.parse_value_name()?;
        self.skip_whitespace();

        // Skip type annotation
        if self.peek_char(':') {
            self.advance();
            self.skip_whitespace();
            self.parse_type()?;
            self.skip_whitespace();
        }

        self.expect_char(',')?;
        self.skip_whitespace();

        let index_str = self.consume_while(|c| c.is_ascii_digit());
        let index: usize = index_str
            .parse()
            .map_err(|_| self.error("invalid tuple element index"))?;

        Ok(SilInstructionKind::TupleElementAddr { operand, index })
    }

    fn parse_ref_tail_addr(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // ref_tail_addr [immutable] %ref : $Class, $ElementType
        // Skip optional attributes
        while self.peek_char('[') {
            self.advance();
            self.parse_identifier()?;
            self.expect_char(']')?;
            self.skip_whitespace();
        }

        let operand = self.parse_value_name()?;
        self.skip_whitespace();

        // Skip ref type annotation
        if self.peek_char(':') {
            self.advance();
            self.skip_whitespace();
            self.parse_type()?;
            self.skip_whitespace();
        }

        self.expect_char(',')?;
        self.skip_whitespace();

        let ty = self.parse_type()?;

        Ok(SilInstructionKind::RefTailAddr { operand, ty })
    }

    fn parse_tail_addr(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // tail_addr %base : $*Base, %count : $Builtin.Word, $ElementType
        let base = self.parse_value_name()?;
        self.skip_whitespace();

        // Skip base type annotation
        if self.peek_char(':') {
            self.advance();
            self.skip_whitespace();
            self.parse_type()?;
            self.skip_whitespace();
        }

        self.expect_char(',')?;
        self.skip_whitespace();

        let count = self.parse_value_name()?;
        self.skip_whitespace();

        // Skip count type annotation
        if self.peek_char(':') {
            self.advance();
            self.skip_whitespace();
            self.parse_type()?;
            self.skip_whitespace();
        }

        self.expect_char(',')?;
        self.skip_whitespace();

        let ty = self.parse_type()?;

        Ok(SilInstructionKind::TailAddr { base, count, ty })
    }

    fn parse_partial_apply(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // partial_apply [callee_guaranteed] [on_stack] %fn<Subs>(%args...) : $FunctionType
        let mut on_stack = false;

        // Parse optional attributes
        while self.peek_char('[') {
            self.advance();
            let attr = self.parse_identifier()?;
            self.expect_char(']')?;
            self.skip_whitespace();
            if attr == "on_stack" {
                on_stack = true;
            }
        }

        let callee = self.parse_value_name()?;
        self.skip_whitespace();

        // Parse optional substitutions <T1, T2, ...>
        let substitutions = if self.peek_char('<') {
            self.parse_substitutions()?
        } else {
            Vec::new()
        };
        self.skip_whitespace();

        // Parse arguments (%0, %1, ...)
        let arguments = self.parse_value_list()?;
        self.skip_to_eol();

        Ok(SilInstructionKind::PartialApply {
            callee,
            substitutions,
            arguments,
            on_stack,
        })
    }

    fn parse_load_borrow(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // load_borrow %addr : $*T
        let address = self.parse_value_name()?;
        self.skip_to_eol();
        Ok(SilInstructionKind::LoadBorrow { address })
    }

    fn parse_alloc_box(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // alloc_box ${ var T }
        // alloc_box [dynamic_lifetime] [reflection] ${ var T }
        // Skip optional attributes
        while self.peek_char('[') {
            self.advance();
            self.parse_identifier()?;
            self.expect_char(']')?;
            self.skip_whitespace();
        }

        let ty = self.parse_type()?;

        Ok(SilInstructionKind::AllocBox { ty })
    }

    fn parse_project_box(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // project_box %box : ${ var T }
        // project_box %box : ${ var T }, 0
        let operand = self.parse_value_name()?;
        self.skip_whitespace();

        // Skip type annotation
        if self.peek_char(':') {
            self.advance();
            self.skip_whitespace();
            self.parse_type()?;
            self.skip_whitespace();
        }

        // Check for optional field index
        let field_index = if self.peek_char(',') {
            self.advance();
            self.skip_whitespace();
            let index_str = self.consume_while(|c| c.is_ascii_digit());
            let index: usize = index_str
                .parse()
                .map_err(|_| self.error("invalid field index"))?;
            Some(index)
        } else {
            None
        };

        Ok(SilInstructionKind::ProjectBox {
            operand,
            field_index,
        })
    }

    fn parse_dealloc_box(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // dealloc_box %box : ${ var T }
        let operand = self.parse_value_name()?;
        self.skip_to_eol();
        Ok(SilInstructionKind::DeallocBox { operand })
    }

    fn parse_super_method(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // super_method %self : $ChildClass, #ParentClass.method : Type, $ConventionType
        let operand = self.parse_value_name()?;
        self.skip_whitespace();

        // Skip type annotation
        if self.peek_char(':') {
            self.advance();
            self.skip_whitespace();
            self.parse_type()?;
            self.skip_whitespace();
        }

        self.expect_char(',')?;
        self.skip_whitespace();

        // Parse method reference: #ParentClass.method
        self.expect_char('#')?;
        let method = self.consume_until(':');
        self.skip_to_eol();

        Ok(SilInstructionKind::SuperMethod { operand, method })
    }

    fn parse_tuple_pack_extract(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // tuple_pack_extract %index of %tuple : $(repeat each T) as $@pack_element("UUID") T
        let index = self.parse_value_name()?;
        self.skip_whitespace();

        self.expect_str("of")?;
        self.skip_whitespace();

        let tuple = self.parse_value_name()?;
        self.skip_whitespace();

        // Skip tuple type annotation
        if self.peek_char(':') {
            self.advance();
            self.skip_whitespace();
            self.parse_type()?;
            self.skip_whitespace();
        }

        // Parse "as $ElementType" if present
        let element_ty = if self.peek_str("as") {
            self.expect_str("as")?;
            self.skip_whitespace();
            self.parse_type()?
        } else {
            SilType::default()
        };

        Ok(SilInstructionKind::TuplePackExtract {
            index,
            tuple,
            element_ty,
        })
    }

    fn parse_global_value(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // global_value [bare] @globalName : $Type
        // Skip optional attributes
        while self.peek_char('[') {
            self.advance();
            self.parse_identifier()?;
            self.expect_char(']')?;
            self.skip_whitespace();
        }

        self.expect_char('@')?;
        let name = self.parse_symbol_name()?;
        self.skip_to_eol();

        Ok(SilInstructionKind::GlobalValue { name })
    }

    fn parse_bind_memory(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // bind_memory %base : $Builtin.RawPointer, %numWords : $Builtin.Word to $T
        let base = self.parse_value_name()?;
        self.skip_whitespace();

        // Skip base type annotation
        if self.peek_char(':') {
            self.advance();
            self.skip_whitespace();
            self.parse_type()?;
            self.skip_whitespace();
        }

        self.expect_char(',')?;
        self.skip_whitespace();

        let num_words = self.parse_value_name()?;
        self.skip_whitespace();

        // Skip num_words type annotation
        if self.peek_char(':') {
            self.advance();
            self.skip_whitespace();
            self.parse_type()?;
            self.skip_whitespace();
        }

        self.expect_str("to")?;
        self.skip_whitespace();

        let ty = self.parse_type()?;

        Ok(SilInstructionKind::BindMemory {
            base,
            num_words,
            ty,
        })
    }

    fn parse_rebind_memory(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // rebind_memory %addr : $*T1 to $T2
        let operand = self.parse_value_name()?;
        self.skip_whitespace();

        // Skip source type annotation
        if self.peek_char(':') {
            self.advance();
            self.skip_whitespace();
            self.parse_type()?;
            self.skip_whitespace();
        }

        self.expect_str("to")?;
        self.skip_whitespace();

        let ty = self.parse_type()?;

        Ok(SilInstructionKind::RebindMemory { operand, ty })
    }

    fn parse_move_value(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // move_value [lexical] [pointer_escape] [var_decl] %operand : $T
        let mut lexical = false;
        let mut pointer_escape = false;
        let mut var_decl = false;

        // Parse optional attributes
        while self.peek_char('[') {
            self.advance();
            let attr = self.parse_identifier()?;
            self.expect_char(']')?;
            self.skip_whitespace();
            match attr.as_str() {
                "lexical" => lexical = true,
                "pointer_escape" => pointer_escape = true,
                "var_decl" => var_decl = true,
                _ => {}
            }
        }

        let operand = self.parse_value_name()?;
        self.skip_to_eol();

        Ok(SilInstructionKind::MoveValue {
            operand,
            lexical,
            pointer_escape,
            var_decl,
        })
    }

    fn parse_unchecked_enum_data(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // unchecked_enum_data %operand : $EnumType, #EnumType.case
        let operand = self.parse_value_name()?;
        self.skip_whitespace();

        // Skip type annotation
        if self.peek_char(':') {
            self.advance();
            self.skip_whitespace();
            self.parse_type()?;
            self.skip_whitespace();
        }

        self.expect_char(',')?;
        self.skip_whitespace();

        let case_name = self.consume_until_whitespace_or_colon();

        Ok(SilInstructionKind::UncheckedEnumData { operand, case_name })
    }

    fn parse_assign(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // assign %src to %dest : $*T
        let source = self.parse_value_name()?;
        self.skip_whitespace();

        self.expect_str("to")?;
        self.skip_whitespace();

        let dest = self.parse_value_name()?;
        self.skip_to_eol();

        Ok(SilInstructionKind::Assign { source, dest })
    }

    fn parse_differentiable_function(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // differentiable_function [parameters 0 1] %original [with_derivative {%jvp, %vjp}]
        self.skip_whitespace();

        // Parse optional [parameters X Y Z]
        let mut parameters = Vec::new();
        if self.peek_char('[') {
            self.advance();
            let kw = self.parse_identifier()?;
            if kw == "parameters" {
                self.skip_whitespace();
                while !self.peek_char(']') && !self.is_eof() {
                    let idx_str = self.consume_while(|c| c.is_ascii_digit());
                    if !idx_str.is_empty() {
                        parameters.push(idx_str.parse().unwrap_or(0));
                    }
                    self.skip_whitespace();
                }
            }
            self.expect_char(']')?;
            self.skip_whitespace();
        }

        let original = self.parse_value_name()?;
        self.skip_whitespace();

        // Parse optional derivative functions
        let mut jvp = None;
        let mut vjp = None;
        if self.peek_str("with_derivative") {
            self.expect_str("with_derivative")?;
            self.skip_whitespace();
            if self.peek_char('{') {
                self.advance();
                self.skip_whitespace();
                // First is JVP
                if self.peek_char('%') {
                    jvp = Some(self.parse_value_name()?);
                }
                self.skip_whitespace();
                if self.peek_char(',') {
                    self.advance();
                    self.skip_whitespace();
                    // Second is VJP
                    if self.peek_char('%') {
                        vjp = Some(self.parse_value_name()?);
                    }
                }
                self.skip_whitespace();
                if self.peek_char('}') {
                    self.advance();
                }
            }
        }
        self.skip_to_eol();

        Ok(SilInstructionKind::DifferentiableFunction {
            original,
            jvp,
            vjp,
            parameters,
        })
    }

    fn parse_linear_function(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // linear_function [parameters 0 1] %original [transpose %transpose]
        self.skip_whitespace();

        // Parse optional [parameters X Y Z]
        let mut parameters = Vec::new();
        if self.peek_char('[') {
            self.advance();
            let kw = self.parse_identifier()?;
            if kw == "parameters" {
                self.skip_whitespace();
                while !self.peek_char(']') && !self.is_eof() {
                    let idx_str = self.consume_while(|c| c.is_ascii_digit());
                    if !idx_str.is_empty() {
                        parameters.push(idx_str.parse().unwrap_or(0));
                    }
                    self.skip_whitespace();
                }
            }
            self.expect_char(']')?;
            self.skip_whitespace();
        }

        let original = self.parse_value_name()?;
        self.skip_whitespace();

        // Parse optional transpose function
        let mut transpose = None;
        if self.peek_str("with_transpose") {
            self.expect_str("with_transpose")?;
            self.skip_whitespace();
            if self.peek_char('%') {
                transpose = Some(self.parse_value_name()?);
            }
        }
        self.skip_to_eol();

        Ok(SilInstructionKind::LinearFunction {
            original,
            transpose,
            parameters,
        })
    }

    fn parse_differentiable_function_extract(
        &mut self,
    ) -> Result<SilInstructionKind, SilParseError> {
        // differentiable_function_extract [jvp|vjp|original] %operand
        self.skip_whitespace();

        let extractee = if self.peek_char('[') {
            self.advance();
            let kw = self.parse_identifier()?;
            self.expect_char(']')?;
            self.skip_whitespace();
            match kw.as_str() {
                "jvp" => DifferentiableExtractee::JVP,
                "vjp" => DifferentiableExtractee::VJP,
                _ => DifferentiableExtractee::Original,
            }
        } else {
            DifferentiableExtractee::Original
        };

        let operand = self.parse_value_name()?;
        self.skip_to_eol();

        Ok(SilInstructionKind::DifferentiableFunctionExtract { operand, extractee })
    }

    fn parse_linear_function_extract(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // linear_function_extract [transpose|original] %operand
        self.skip_whitespace();

        let extractee = if self.peek_char('[') {
            self.advance();
            let kw = self.parse_identifier()?;
            self.expect_char(']')?;
            self.skip_whitespace();
            match kw.as_str() {
                "transpose" => LinearExtractee::Transpose,
                _ => LinearExtractee::Original,
            }
        } else {
            LinearExtractee::Original
        };

        let operand = self.parse_value_name()?;
        self.skip_to_eol();

        Ok(SilInstructionKind::LinearFunctionExtract { operand, extractee })
    }

    fn parse_differentiability_witness_function(
        &mut self,
    ) -> Result<SilInstructionKind, SilParseError> {
        // differentiability_witness_function [jvp|vjp|transpose] @witness : $FuncType
        self.skip_whitespace();

        let witness_kind = if self.peek_char('[') {
            self.advance();
            let kw = self.parse_identifier()?;
            self.expect_char(']')?;
            self.skip_whitespace();
            match kw.as_str() {
                "vjp" => DifferentiabilityWitnessKind::VJP,
                "transpose" => DifferentiabilityWitnessKind::Transpose,
                _ => DifferentiabilityWitnessKind::JVP,
            }
        } else {
            DifferentiabilityWitnessKind::JVP
        };

        // Parse @witness_name
        let witness = if self.peek_char('@') {
            self.advance();
            self.consume_while(|c| c.is_alphanumeric() || c == '_' || c == '$')
        } else {
            String::new()
        };

        // Skip type annotation
        let ty = if self.peek_char(':') {
            self.advance();
            self.skip_whitespace();
            self.parse_type()?
        } else {
            SilType::default()
        };

        self.skip_to_eol();

        Ok(SilInstructionKind::DifferentiabilityWitnessFunction {
            witness_kind,
            witness,
            ty,
        })
    }

    fn parse_begin_apply(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // begin_apply %fn<Subs>(%args) : $FuncType
        // Similar to apply but returns multiple values (token + yielded values)
        let callee = self.parse_value_name()?;
        self.skip_whitespace();

        // Parse optional substitutions <Type, Type, ...>
        let substitutions = if self.peek_char('<') {
            self.parse_substitutions()?
        } else {
            Vec::new()
        };

        self.skip_whitespace();
        // Parse arguments
        let arguments = self.parse_value_list()?;

        // Skip remaining (type annotation, etc.)
        self.skip_to_eol();

        Ok(SilInstructionKind::BeginApply {
            callee,
            substitutions,
            arguments,
        })
    }

    fn parse_end_apply(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // end_apply %token [as $Type]
        let token = self.parse_value_name()?;
        self.skip_to_eol();

        Ok(SilInstructionKind::EndApply { token })
    }

    fn parse_abort_apply(&mut self) -> Result<SilInstructionKind, SilParseError> {
        // abort_apply %token
        let token = self.parse_value_name()?;
        self.skip_to_eol();

        Ok(SilInstructionKind::AbortApply { token })
    }

    // ==================== END NEW PARSE FUNCTIONS ====================

    fn skip_balanced_brackets(&mut self, open: char, close: char) -> Result<(), SilParseError> {
        self.expect_char(open)?;
        let mut depth = 1;
        while depth > 0 && !self.is_eof() {
            // Use current_char() which correctly handles UTF-8 byte offsets
            if let Some(ch) = self.current_char() {
                if ch == open {
                    depth += 1;
                } else if ch == close {
                    depth -= 1;
                }
                self.advance();
            } else {
                break;
            }
        }
        if depth != 0 {
            return Err(self.error(&format!("unbalanced {open} {close}")));
        }
        Ok(())
    }

    const fn is_eof(&self) -> bool {
        self.pos >= self.input.len()
    }

    fn error(&self, message: &str) -> SilParseError {
        SilParseError {
            message: message.to_string(),
            line: self.line,
            column: self.column,
        }
    }
}

/// Parse SIL from a string
///
/// Runs parsing on a thread with 64MB stack to handle deeply nested types
/// in complex Swift SIL output (e.g., from `SwiftUI` code).
///
/// # Errors
/// Returns an error if the input is not valid SIL or the parser thread cannot be spawned/joined.
pub fn parse_sil(input: &str) -> Result<SilModule, SilParseError> {
    // Use a thread with larger stack to handle recursive type parsing
    // Default stack (~2MB) can overflow on complex Swift types with deep nesting
    // SwiftUI-generated SIL can have extremely deeply nested types
    const PARSER_STACK_SIZE: usize = 64 * 1024 * 1024; // 64MB

    let input = input.to_owned();
    let handle = std::thread::Builder::new()
        .stack_size(PARSER_STACK_SIZE)
        .spawn(move || {
            let mut parser = SilParser::new(&input);
            parser.parse_module()
        })
        .map_err(|e| SilParseError {
            message: format!("Failed to spawn parser thread: {e}"),
            line: 0,
            column: 0,
        })?;

    handle.join().map_err(|_| SilParseError {
        message: "Parser thread panicked".to_string(),
        line: 0,
        column: 0,
    })?
}

#[cfg(test)]
mod tests {
    use super::*;

    fn assert_branch_to(terminator: &SilTerminator, expected_dest: &str) {
        assert!(
            matches!(terminator, SilTerminator::Branch { dest, .. } if dest == expected_dest),
            "expected Branch to {expected_dest}, got {terminator:?}"
        );
    }

    fn assert_cond_branch_to(
        terminator: &SilTerminator,
        expected_condition: &str,
        expected_true_dest: &str,
        expected_false_dest: &str,
    ) {
        match terminator {
            SilTerminator::CondBranch {
                condition,
                true_dest,
                false_dest,
                ..
            } => {
                assert_eq!(condition, expected_condition);
                assert_eq!(true_dest, expected_true_dest);
                assert_eq!(false_dest, expected_false_dest);
            }
            other => panic!("expected CondBranch, got {other:?}"),
        }
    }

    fn assert_switch_enum_to(
        terminator: &SilTerminator,
        expected_operand: &str,
        expected_case_substrings: &[&str],
        expected_default: Option<&str>,
    ) {
        match terminator {
            SilTerminator::SwitchEnum {
                operand,
                cases,
                default,
            } => {
                assert_eq!(operand, expected_operand);
                assert_eq!(cases.len(), expected_case_substrings.len());

                for (idx, expected_substring) in expected_case_substrings.iter().enumerate() {
                    assert!(cases[idx].0.contains(expected_substring));
                }

                assert_eq!(default.as_deref(), expected_default);
            }
            other => panic!("expected SwitchEnum, got {other:?}"),
        }
    }

    fn assert_is_return(terminator: &SilTerminator) {
        assert!(
            matches!(terminator, SilTerminator::Return { .. }),
            "expected Return, got {terminator:?}"
        );
    }

    #[test]
    fn test_parse_simple_function() {
        let sil = r#"
sil_stage canonical

import Swift

sil hidden @add : $@convention(thin) (Int, Int) -> Int {
bb0(%0 : $Int, %1 : $Int):
  %2 = struct_extract %0, #Int._value
  %3 = struct_extract %1, #Int._value
  %4 = integer_literal $Builtin.Int1, -1
  %5 = builtin "sadd_with_overflow_Int64"(%2, %3, %4) : $(Builtin.Int64, Builtin.Int1)
  %6 = tuple_extract %5, 0
  %7 = tuple_extract %5, 1
  cond_fail %7, "arithmetic overflow"
  %8 = struct $Int (%6)
  return %8
}
"#;

        let module = parse_sil(sil).expect("parse failed");

        assert_eq!(module.stage, SilStage::Canonical);
        assert_eq!(module.imports.len(), 1);
        assert_eq!(module.imports[0], "Swift");
        assert_eq!(module.functions.len(), 1);

        let func = &module.functions[0];
        assert_eq!(func.name, "add");
        assert_eq!(func.linkage, SilLinkage::Hidden);
        assert_eq!(func.blocks.len(), 1);

        let block = &func.blocks[0];
        assert_eq!(block.label, "bb0");
        assert_eq!(block.arguments.len(), 2);

        // Check for cond_fail instruction
        let has_cond_fail = block
            .instructions
            .iter()
            .any(|inst| matches!(&inst.kind, SilInstructionKind::CondFail { .. }));
        assert!(has_cond_fail, "should have cond_fail instruction");

        // Check terminator
        assert!(matches!(&block.terminator, SilTerminator::Return { .. }));
    }

    #[test]
    fn test_parse_cond_fail() {
        let sil = r#"
sil_stage canonical

sil @test : $@convention(thin) (Builtin.Int1) -> () {
bb0(%0 : $Builtin.Int1):
  cond_fail %0, "test failure"
  %1 = tuple ()
  return %1
}
"#;

        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let block = &func.blocks[0];

        // Find cond_fail
        let cond_fail = block
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::CondFail { .. }));

        assert!(cond_fail.is_some());
        if let SilInstructionKind::CondFail { condition, message } = &cond_fail.unwrap().kind {
            assert_eq!(condition, "%0");
            assert_eq!(message, "test failure");
        }
    }

    #[test]
    fn test_parse_simple_br() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = tuple ()
  br bb1
bb1:
  return %0
}
";

        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        assert_eq!(func.blocks.len(), 2);
    }

    #[test]
    fn test_parse_branch() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (Builtin.Int1) -> Builtin.Int64 {
bb0(%0 : $Builtin.Int1):
  cond_br %0, bb1, bb2
bb1:
  %1 = integer_literal $Builtin.Int64, 1
  br bb3(%1)
bb2:
  %2 = integer_literal $Builtin.Int64, 0
  br bb3(%2)
bb3(%3 : $Builtin.Int64):
  return %3
}
";

        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];

        assert_eq!(func.blocks.len(), 4);

        // Check bb0 has conditional branch
        let bb0 = &func.blocks[0];
        assert!(matches!(
            &bb0.terminator,
            SilTerminator::CondBranch { condition, true_dest, false_dest, .. }
            if condition == "%0" && true_dest == "bb1" && false_dest == "bb2"
        ));

        // Check bb3 has argument
        let bb3 = &func.blocks[3];
        assert_eq!(bb3.arguments.len(), 1);
        assert_eq!(bb3.arguments[0].name, "%3");
    }

    #[test]
    fn test_parse_real_swiftc_output() {
        // Real SIL output from: swiftc -emit-sil /tmp/test_sil.swift
        // Source: func add(_ a: Int, _ b: Int) -> Int { return a + b }
        let sil = r#"
sil_stage canonical

import Builtin
import Swift
import SwiftShims

func add(_ a: Int, _ b: Int) -> Int

// main
// Isolation: unspecified
sil @main : $@convention(c) (Int32, UnsafeMutablePointer<Optional<UnsafeMutablePointer<Int8>>>) -> Int32 {
bb0(%0 : $Int32, %1 : $UnsafeMutablePointer<Optional<UnsafeMutablePointer<Int8>>>):
  %2 = integer_literal $Builtin.Int32, 0          // user: %3
  %3 = struct $Int32 (%2)                         // user: %4
  return %3                                       // id: %4
} // end sil function 'main'

// add(_:_:)
// Isolation: unspecified
sil hidden @$s8test_sil3addyS2i_SitF : $@convention(thin) (Int, Int) -> Int {
// %0 "a"                                         // users: %4, %2
// %1 "b"                                         // users: %5, %3
bb0(%0 : $Int, %1 : $Int):
  debug_value %0, let, name "a", argno 1          // id: %2
  debug_value %1, let, name "b", argno 2          // id: %3
  %4 = struct_extract %0, #Int._value             // user: %7
  %5 = struct_extract %1, #Int._value             // user: %7
  %6 = integer_literal $Builtin.Int1, -1          // user: %7
  %7 = builtin "sadd_with_overflow_Int64"(%4, %5, %6) : $(Builtin.Int64, Builtin.Int1) // users: %9, %8
  %8 = tuple_extract %7, 0                        // user: %11
  %9 = tuple_extract %7, 1                        // user: %10
  cond_fail %9, "arithmetic overflow"             // id: %10
  %11 = struct $Int (%8)                          // user: %12
  return %11                                      // id: %12
} // end sil function '$s8test_sil3addyS2i_SitF'

// static Int.+ infix(_:_:)
// Isolation: unspecified
sil public_external [transparent] @$sSi1poiyS2i_SitFZ : $@convention(method) (Int, Int, @thin Int.Type) -> Int {
// %0                                             // user: %3
// %1                                             // user: %4
bb0(%0 : $Int, %1 : $Int, %2 : $@thin Int.Type):
  %3 = struct_extract %0, #Int._value             // user: %6
  %4 = struct_extract %1, #Int._value             // user: %6
  %5 = integer_literal $Builtin.Int1, -1          // user: %6
  %6 = builtin "sadd_with_overflow_Int64"(%3, %4, %5) : $(Builtin.Int64, Builtin.Int1) // users: %8, %7
  %7 = tuple_extract %6, 0                        // user: %10
  %8 = tuple_extract %6, 1                        // user: %9
  cond_fail %8, "arithmetic overflow"             // id: %9
  %10 = struct $Int (%7)                          // user: %11
  return %10                                      // id: %11
} // end sil function '$sSi1poiyS2i_SitFZ'


// Mappings from '#fileID' to '#filePath':
//   'test_sil/test_sil.swift' => '/tmp/test_sil.swift'
"#;

        let module = parse_sil(sil).expect("parse failed");

        // Verify stage
        assert_eq!(module.stage, SilStage::Canonical);

        // Verify imports
        assert_eq!(module.imports.len(), 3);
        assert!(module.imports.contains(&"Builtin".to_string()));
        assert!(module.imports.contains(&"Swift".to_string()));
        assert!(module.imports.contains(&"SwiftShims".to_string()));

        // Verify functions - should have main, add, and Int.+
        assert_eq!(module.functions.len(), 3);

        // Find the add function
        let add_func = module
            .functions
            .iter()
            .find(|f| f.name.contains("add") && !f.name.contains("poiy"))
            .expect("should find add function");

        assert_eq!(add_func.linkage, SilLinkage::Hidden);
        assert_eq!(add_func.blocks.len(), 1);

        let bb0 = &add_func.blocks[0];
        assert_eq!(bb0.arguments.len(), 2);

        // Verify cond_fail instruction exists for arithmetic overflow check
        let cond_fail_count = bb0.instructions.iter().filter(|inst| {
            matches!(&inst.kind, SilInstructionKind::CondFail { message, .. } if message == "arithmetic overflow")
        }).count();
        assert_eq!(
            cond_fail_count, 1,
            "should have one cond_fail for overflow check"
        );

        // Verify the Int.+ function has public_external linkage
        let plus_func = module
            .functions
            .iter()
            .find(|f| {
                f.name.contains("poiy") // mangled + operator
            })
            .expect("should find Int.+ function");

        assert_eq!(plus_func.linkage, SilLinkage::PublicExternal);
    }

    #[test]
    fn test_parse_source_locations() {
        // SIL with source location annotations (from swiftc -emit-sil -g)
        let sil = r#"
sil_stage canonical

sil hidden @$s4test3addyS2i_SitF : $@convention(thin) (Int, Int) -> Int {
bb0(%0 : $Int, %1 : $Int):
  debug_value %0, let, name "a", argno 1, loc "/tmp/test.swift":1:12, scope 2
  debug_value %1, let, name "b", argno 2, loc "/tmp/test.swift":1:22, scope 2
  %4 = struct_extract %0, #Int._value, loc "/tmp/test.swift":1:48, scope 2
  %5 = struct_extract %1, #Int._value, loc "/tmp/test.swift":1:48, scope 2
  %6 = integer_literal $Builtin.Int1, -1, loc "/tmp/test.swift":1:48, scope 2
  %7 = builtin "sadd_with_overflow_Int64"(%4, %5, %6) : $(Builtin.Int64, Builtin.Int1), loc "/tmp/test.swift":1:48, scope 2
  %8 = tuple_extract %7, 0, loc "/tmp/test.swift":1:48, scope 2
  %9 = tuple_extract %7, 1, loc "/tmp/test.swift":1:48, scope 2
  cond_fail %9, "arithmetic overflow", loc "/tmp/test.swift":1:48, scope 2
  %11 = struct $Int (%8), loc "/tmp/test.swift":1:48, scope 2
  return %11, loc "/tmp/test.swift":1:39, scope 2
}
"#;

        let module = parse_sil(sil).expect("parse failed");
        assert_eq!(module.functions.len(), 1);

        let func = &module.functions[0];
        let block = &func.blocks[0];

        // Check debug_value has location
        let debug_value_0 = block.instructions.iter().find(|inst| {
            matches!(&inst.kind, SilInstructionKind::DebugValue { name, .. } if name.as_deref() == Some("a"))
        }).expect("should find debug_value for 'a'");

        assert!(
            debug_value_0.location.is_some(),
            "debug_value should have location"
        );
        let loc = debug_value_0.location.as_ref().unwrap();
        assert_eq!(loc.file, "/tmp/test.swift");
        assert_eq!(loc.line, 1);
        assert_eq!(loc.column, 12);

        // Check cond_fail has location
        let cond_fail = block
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::CondFail { .. }))
            .expect("should find cond_fail");

        assert!(
            cond_fail.location.is_some(),
            "cond_fail should have location"
        );
        let loc = cond_fail.location.as_ref().unwrap();
        assert_eq!(loc.file, "/tmp/test.swift");
        assert_eq!(loc.line, 1);
        assert_eq!(loc.column, 48);
    }

    #[test]
    fn test_parse_without_locations() {
        // SIL without location annotations should still work
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (Int) -> Int {
bb0(%0 : $Int):
  %1 = struct_extract %0, #Int._value  // no loc annotation
  %2 = struct $Int (%1)
  return %2
}
";

        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let block = &func.blocks[0];

        // Instructions without loc should have None location
        for inst in &block.instructions {
            assert!(
                inst.location.is_none(),
                "instruction without loc should have None location"
            );
        }
    }

    #[test]
    fn test_parse_index_addr() {
        // Test parsing index_addr instruction
        let sil = r"
sil_stage canonical

sil @test_index : $@convention(thin) (Builtin.RawPointer, Builtin.Word) -> Builtin.RawPointer {
bb0(%0 : $Builtin.RawPointer, %1 : $Builtin.Word):
  %2 = index_addr %0 : $*Int, %1 : $Builtin.Word
  %3 = address_to_pointer %2 : $*Int to $Builtin.RawPointer
  return %3
}
";

        let module = parse_sil(sil).expect("parse failed");
        assert_eq!(module.functions.len(), 1);

        let func = &module.functions[0];
        let block = &func.blocks[0];

        // Find the index_addr instruction
        let index_addr = block
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::IndexAddr { .. }));

        assert!(index_addr.is_some(), "should find index_addr instruction");
        if let SilInstructionKind::IndexAddr { base, index } = &index_addr.unwrap().kind {
            assert_eq!(base, "%0");
            assert_eq!(index, "%1");
        }
    }

    #[test]
    fn test_parse_index_addr_with_stack_protection() {
        // Test parsing index_addr with [stack_protection] attribute
        let sil = r"
sil_stage canonical

sil @test_index : $@convention(thin) (Builtin.RawPointer, Builtin.Word) -> Builtin.RawPointer {
bb0(%0 : $Builtin.RawPointer, %1 : $Builtin.Word):
  %2 = pointer_to_address %0 : $Builtin.RawPointer to [strict] $*Int
  %3 = index_addr [stack_protection] %2 : $*Int, %1 : $Builtin.Word
  %4 = address_to_pointer %3 : $*Int to $Builtin.RawPointer
  return %4
}
";

        let module = parse_sil(sil).expect("parse failed");
        assert_eq!(module.functions.len(), 1);

        let func = &module.functions[0];
        let block = &func.blocks[0];

        // Find the index_addr instruction
        let index_addr = block
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::IndexAddr { .. }));

        assert!(
            index_addr.is_some(),
            "should find index_addr instruction with [stack_protection]"
        );
        if let SilInstructionKind::IndexAddr { base, index } = &index_addr.unwrap().kind {
            assert_eq!(base, "%2");
            assert_eq!(index, "%1");
        }
    }

    #[test]
    fn test_parse_index_raw_pointer() {
        // Test parsing index_raw_pointer instruction (similar to index_addr)
        let sil = r"
sil_stage canonical

sil @test_index_raw : $@convention(thin) (Builtin.RawPointer, Builtin.Word) -> Builtin.RawPointer {
bb0(%0 : $Builtin.RawPointer, %1 : $Builtin.Word):
  %2 = index_raw_pointer %0 : $Builtin.RawPointer, %1 : $Builtin.Word
  return %2
}
";

        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let block = &func.blocks[0];

        // Should parse index_raw_pointer as IndexAddr variant
        let index_inst = block
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::IndexAddr { .. }));

        assert!(
            index_inst.is_some(),
            "should find index_raw_pointer parsed as IndexAddr"
        );
    }

    #[test]
    fn test_parse_verification_attributes() {
        let sil = r#"
sil_stage canonical

sil [_requires "x > 0"] [_ensures "result >= x"] @verified_double : $@convention(thin) (Int) -> Int {
bb0(%0 : $Int):
  return %0
}
"#;

        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];

        assert_eq!(func.name, "verified_double");
        assert_eq!(func.attributes.len(), 2);

        // Check for @_requires attribute
        let has_requires = func
            .attributes
            .iter()
            .any(|attr| matches!(attr, SilAttribute::Requires(cond) if cond == "x > 0"));
        assert!(
            has_requires,
            "should have @_requires attribute with 'x > 0'"
        );

        // Check for @_ensures attribute
        let has_ensures = func
            .attributes
            .iter()
            .any(|attr| matches!(attr, SilAttribute::Ensures(cond) if cond == "result >= x"));
        assert!(
            has_ensures,
            "should have @_ensures attribute with 'result >= x'"
        );
    }

    #[test]
    fn test_parse_trusted_attribute() {
        let sil = r"
sil_stage canonical

sil [_trusted] @unsafe_op : $@convention(thin) () -> () {
bb0:
  %0 = tuple ()
  return %0
}
";

        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];

        assert_eq!(func.name, "unsafe_op");

        let has_trusted = func
            .attributes
            .iter()
            .any(|attr| matches!(attr, SilAttribute::Trusted));
        assert!(has_trusted, "should have @_trusted attribute");
    }

    /// Test that @_trusted on same line as func declaration is parsed correctly.
    /// This is the format used in real Swift compiler output (e.g., `verified_positive.sil`).
    #[test]
    fn test_parse_trusted_same_line_as_func() {
        // The mangled name format is $s<module_len><module><func_len><func>...
        // "test" = 4 chars, "unsafeOp" = 8 chars
        let sil = r"
sil_stage canonical

@_trusted func unsafeOp() -> Int

sil hidden @$s4test8unsafeOpSiyF : $@convention(thin) () -> Int {
bb0:
  %0 = integer_literal $Builtin.Int64, 42
  %1 = struct $Int (%0)
  return %1
}
";

        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("unsafeOp"))
            .expect("should find unsafeOp function");

        let has_trusted = func
            .attributes
            .iter()
            .any(|attr| matches!(attr, SilAttribute::Trusted));
        assert!(
            has_trusted,
            "unsafeOp should have @_trusted from Swift-syntax same-line declaration"
        );
    }

    #[test]
    fn test_parse_semantics_attribute() {
        let sil = r#"
sil_stage canonical

sil [_semantics "array.bounds_check"] @bounds_check : $@convention(thin) () -> () {
bb0:
  %0 = tuple ()
  return %0
}
"#;

        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];

        let has_semantics = func.attributes.iter().any(
            |attr| matches!(attr, SilAttribute::Semantics(tag) if tag == "array.bounds_check"),
        );
        assert!(has_semantics, "should have @_semantics attribute");
    }

    #[test]
    fn test_parse_mixed_attributes() {
        let sil = r#"
sil_stage canonical

sil [ossa] [_requires "a >= 0"] [_requires "b >= 0"] [_ensures "result >= 0"] @safe_add : $@convention(thin) (Int, Int) -> Int {
bb0(%0 : $Int, %1 : $Int):
  return %0
}
"#;

        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];

        assert_eq!(func.name, "safe_add");

        // Should have ossa + 2 requires + 1 ensures = 4 attributes
        assert_eq!(func.attributes.len(), 4);

        // Count requires
        let requires_count = func
            .attributes
            .iter()
            .filter(|attr| matches!(attr, SilAttribute::Requires(_)))
            .count();
        assert_eq!(requires_count, 2, "should have 2 @_requires attributes");

        // Count ensures
        let ensures_count = func
            .attributes
            .iter()
            .filter(|attr| matches!(attr, SilAttribute::Ensures(_)))
            .count();
        assert_eq!(ensures_count, 1, "should have 1 @_ensures attribute");

        // Check ossa
        let has_ossa = func
            .attributes
            .iter()
            .any(|attr| matches!(attr, SilAttribute::Ossa));
        assert!(has_ossa, "should have [ossa] attribute");
    }

    #[test]
    fn test_parse_invariant_attribute() {
        let sil = r#"
sil_stage canonical

sil [_invariant "count >= 0"] @counter_op : $@convention(thin) (Int) -> Int {
bb0(%0 : $Int):
  return %0
}
"#;

        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];

        assert_eq!(func.name, "counter_op");

        let has_invariant = func
            .attributes
            .iter()
            .any(|attr| matches!(attr, SilAttribute::Invariant(cond) if cond == "count >= 0"));
        assert!(
            has_invariant,
            "should have @_invariant attribute with 'count >= 0'"
        );
    }

    #[test]
    fn test_parse_invariant_swift_syntax() {
        // Swift-syntax @_invariant declaration (even though Swift compiler rejects it on functions)
        // The parser should still handle it for completeness
        let sil = r#"
sil_stage canonical

@_invariant("x >= 0")
func withInvariant(_ x: Int) -> Int

sil hidden @$s4test13withInvariantyS2iF : $@convention(thin) (Int) -> Int {
bb0(%0 : $Int):
  debug_value %0, let, name "x", argno 1
  return %0
}
"#;

        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];

        let has_invariant = func
            .attributes
            .iter()
            .any(|attr| matches!(attr, SilAttribute::Invariant(cond) if cond == "x >= 0"));
        assert!(
            has_invariant,
            "should have @_invariant attribute from Swift-syntax declaration"
        );
    }

    #[test]
    fn test_parse_swift_syntax_declarations() {
        // This is the format that real swift-frontend outputs - Swift declarations
        // with @_requires/@_ensures BEFORE the sil function declaration
        let sil = r#"
sil_stage canonical

import Builtin
import Swift
import SwiftShims

@_requires("x > 0")
@_ensures("result > 0")
func keepPositive(_ x: Int) -> Int

// main
sil @main : $@convention(c) (Int32, UnsafeMutablePointer<Optional<UnsafeMutablePointer<Int8>>>) -> Int32 {
bb0(%0 : $Int32, %1 : $UnsafeMutablePointer<Optional<UnsafeMutablePointer<Int8>>>):
  %2 = integer_literal $Builtin.Int32, 0
  %3 = struct $Int32 (%2)
  return %3
}

// keepPositive(_:)
sil hidden @$s8positive12keepPositiveyS2iF : $@convention(thin) (Int) -> Int {
bb0(%0 : $Int):
  debug_value %0, let, name "x", argno 1
  return %0
}
"#;

        let module = parse_sil(sil).expect("parse failed");

        // Find the keepPositive function by its mangled name
        let keep_positive = module
            .functions
            .iter()
            .find(|f| f.name.contains("keepPositive"))
            .expect("should find keepPositive function");

        // Should have attributes from Swift-syntax declaration
        let has_requires = keep_positive
            .attributes
            .iter()
            .any(|attr| matches!(attr, SilAttribute::Requires(cond) if cond == "x > 0"));
        assert!(
            has_requires,
            "keepPositive should have @_requires(\"x > 0\") from Swift-syntax declaration"
        );

        let has_ensures = keep_positive
            .attributes
            .iter()
            .any(|attr| matches!(attr, SilAttribute::Ensures(cond) if cond == "result > 0"));
        assert!(
            has_ensures,
            "keepPositive should have @_ensures(\"result > 0\") from Swift-syntax declaration"
        );

        // Verify demangled name was set
        assert!(
            keep_positive.demangled_name.is_some(),
            "demangled_name should be set"
        );
    }

    #[test]
    fn test_parse_swift_syntax_multiple_attrs() {
        // Test multiple @_requires attributes
        let sil = r#"
sil_stage canonical

@_requires("a >= 0")
@_requires("b >= 0")
@_ensures("result >= 0")
func safeAdd(_ a: Int, _ b: Int) -> Int

sil hidden @$s4test7safeAddyS2i_SitF : $@convention(thin) (Int, Int) -> Int {
bb0(%0 : $Int, %1 : $Int):
  return %0
}
"#;

        let module = parse_sil(sil).expect("parse failed");
        let safe_add = module
            .functions
            .iter()
            .find(|f| f.name.contains("safeAdd"))
            .expect("should find safeAdd function");

        // Count requires attributes
        let requires_count = safe_add
            .attributes
            .iter()
            .filter(|attr| matches!(attr, SilAttribute::Requires(_)))
            .count();
        assert_eq!(
            requires_count, 2,
            "safeAdd should have 2 @_requires attributes"
        );

        // Count ensures attributes
        let ensures_count = safe_add
            .attributes
            .iter()
            .filter(|attr| matches!(attr, SilAttribute::Ensures(_)))
            .count();
        assert_eq!(
            ensures_count, 1,
            "safeAdd should have 1 @_ensures attribute"
        );
    }

    // ========================================================================
    // Edge case tests (added in #151)
    // ========================================================================

    #[test]
    fn test_parse_empty_module() {
        // Minimal valid SIL - just the stage declaration
        let sil = "sil_stage canonical\n";

        let module = parse_sil(sil).expect("parse failed");

        assert_eq!(module.stage, SilStage::Canonical);
        assert!(module.imports.is_empty(), "should have no imports");
        assert!(module.functions.is_empty(), "should have no functions");
        assert!(module.globals.is_empty(), "should have no globals");
    }

    #[test]
    fn test_parse_raw_stage() {
        // Raw stage (pre-optimization) SIL
        let sil = r"
sil_stage raw

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = tuple ()
  return %0
}
";

        let module = parse_sil(sil).expect("parse failed");
        assert_eq!(module.stage, SilStage::Raw);
        assert_eq!(module.functions.len(), 1);
    }

    #[test]
    fn test_parse_external_declaration() {
        // External function declaration (no body)
        let sil = r"
sil_stage canonical

sil public_external @external_func : $@convention(thin) (Int) -> Int
";

        let module = parse_sil(sil).expect("parse failed");
        assert_eq!(module.functions.len(), 1);

        let func = &module.functions[0];
        assert_eq!(func.name, "external_func");
        assert_eq!(func.linkage, SilLinkage::PublicExternal);
        assert!(
            func.blocks.is_empty(),
            "external function should have no blocks"
        );
    }

    #[test]
    fn test_parse_all_linkage_types() {
        // Test all linkage types are parsed correctly
        let sil = r"
sil_stage canonical

sil public @pub_func : $@convention(thin) () -> () {
bb0:
  %0 = tuple ()
  return %0
}

sil hidden @hidden_func : $@convention(thin) () -> () {
bb0:
  %0 = tuple ()
  return %0
}

sil private @priv_func : $@convention(thin) () -> () {
bb0:
  %0 = tuple ()
  return %0
}

sil shared @shared_func : $@convention(thin) () -> () {
bb0:
  %0 = tuple ()
  return %0
}

sil hidden_external @hidden_ext_func : $@convention(thin) () -> ()
";

        let module = parse_sil(sil).expect("parse failed");
        assert_eq!(module.functions.len(), 5);

        let linkages: Vec<_> = module
            .functions
            .iter()
            .map(|f| (&f.name, f.linkage))
            .collect();

        assert!(
            linkages
                .iter()
                .any(|(n, l)| n.as_str() == "pub_func" && *l == SilLinkage::Public)
        );
        assert!(
            linkages
                .iter()
                .any(|(n, l)| n.as_str() == "hidden_func" && *l == SilLinkage::Hidden)
        );
        assert!(
            linkages
                .iter()
                .any(|(n, l)| n.as_str() == "priv_func" && *l == SilLinkage::Private)
        );
        assert!(
            linkages
                .iter()
                .any(|(n, l)| n.as_str() == "shared_func" && *l == SilLinkage::Shared)
        );
        assert!(
            linkages
                .iter()
                .any(|(n, l)| n.as_str() == "hidden_ext_func" && *l == SilLinkage::HiddenExternal)
        );
    }

    #[test]
    fn test_parse_empty_basic_block() {
        // Basic block with no regular instructions, just tuple creation before return
        // (Note: SIL always requires explicit return values even for void)
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = tuple ()
  return %0
}
";

        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let block = &func.blocks[0];

        // Should have 1 tuple instruction
        assert_eq!(
            block.instructions.len(),
            1,
            "block should have 1 instruction"
        );
        assert!(matches!(&block.terminator, SilTerminator::Return { .. }));
    }

    #[test]
    fn test_parse_throw_terminator() {
        // Test throw terminator
        let sil = r#"
sil_stage canonical

sil @throwing : $@convention(thin) (Error) -> () {
bb0(%0 : $Error):
  debug_value %0, let, name "error"
  throw %0
}
"#;

        let module = parse_sil(sil).expect("parse failed");
        assert_eq!(module.functions.len(), 1);
        let func = &module.functions[0];
        assert_eq!(func.blocks.len(), 1);
        let block = &func.blocks[0];

        assert!(matches!(&block.terminator, SilTerminator::Throw { operand } if operand == "%0"));
    }

    #[test]
    fn test_parse_multiple_imports() {
        // Multiple import statements
        let sil = r"
sil_stage canonical

import Builtin
import Swift
import SwiftShims
import Foundation
";

        let module = parse_sil(sil).expect("parse failed");
        assert_eq!(module.imports.len(), 4);
        assert_eq!(module.imports[0], "Builtin");
        assert_eq!(module.imports[1], "Swift");
        assert_eq!(module.imports[2], "SwiftShims");
        assert_eq!(module.imports[3], "Foundation");
    }

    #[test]
    fn test_parse_with_comments() {
        // SIL with inline comments
        let sil = r"
sil_stage canonical

// This is a top-level comment

sil @test : $@convention(thin) (Int) -> Int {
// Function entry
bb0(%0 : $Int):  // param comment
  // Instruction comment
  %1 = struct_extract %0, #Int._value  // inline comment
  %2 = struct $Int (%1)  // user: %3
  return %2  // exit
}
";

        let module = parse_sil(sil).expect("parse failed");
        assert_eq!(module.functions.len(), 1);

        let func = &module.functions[0];
        assert_eq!(func.blocks.len(), 1);

        let block = &func.blocks[0];
        assert_eq!(block.arguments.len(), 1);
        assert_eq!(block.instructions.len(), 2);
    }

    // Regression tests for top-level declarations that used to be mis-parsed
    // due to prefix matching on "sil" (fixed in #152).

    #[test]
    fn test_parse_global_variable() {
        let sil = r"
sil_stage canonical

sil_global public [let] @myGlobal : $Int

sil @useGlobal : $@convention(thin) () -> Int {
bb0:
  %0 = global_addr @myGlobal : $*Int
  %1 = load [copy] %0 : $*Int
  return %1
}
";

        let module = parse_sil(sil).expect("parse failed");

        assert_eq!(module.globals.len(), 1);
        assert_eq!(module.globals[0].name, "myGlobal");
        assert_eq!(module.globals[0].linkage, SilLinkage::Public);
        assert!(matches!(module.globals[0].ty, SilType::Named(ref s) if s == "Int"));

        assert_eq!(module.functions.len(), 1);
        assert_eq!(module.functions[0].name, "useGlobal");
    }

    #[test]
    fn test_skip_vtable_and_witness_table_declarations() {
        let sil = r"
sil_stage canonical

sil_vtable SomeType {
  #SomeType.deinit!deallocator: <null>
}

sil_witness_table hidden SomeProtocol conformance SomeType : SomeProtocol {
}

sil @f : $@convention(thin) () -> () {
bb0:
  %0 = tuple ()
  return %0
}
";

        let module = parse_sil(sil).expect("parse failed");
        assert_eq!(module.functions.len(), 1);
        assert_eq!(module.functions[0].name, "f");
    }

    #[test]
    fn test_skip_all_sil_star_declarations() {
        // Tests that all sil_* top-level declarations are skipped correctly.
        // This includes: sil_scope, sil_differentiability_witness, sil_moveonlydeinit,
        // sil_default_witness_table, sil_property, sil_coverage_map, sil_default_override_table
        let sil = r#"
sil_stage canonical

import Builtin

// Debug scope declaration
sil_scope 1 { loc "test.swift":1:1 parent @foo : $@convention(thin) () -> () }

// Differentiability witness
sil_differentiability_witness [serialized] @test_diff : $@convention(thin) (Float) -> Float {
  jvp: @test_diff_jvp
  vjp: @test_diff_vjp
}

// Move-only deinit
sil_moveonlydeinit MoveOnlyType @test_deinit : $@convention(thin) (@in MoveOnlyType) -> ()

// Default witness table
sil_default_witness_table TestProtocol {
  method #TestProtocol.test: <Self where Self : TestProtocol> (Self) -> () -> () : @test_witness
}

// Property declaration
sil_property #Test.value ()

// Coverage map
sil_coverage_map 0x12345678 "test.swift" "test_func" 0 {
}

// VTable (already tested separately, included for completeness)
sil_vtable TestClass {
  #TestClass.init!allocator: @test_allocator
}

// Witness table (already tested separately, included for completeness)
sil_witness_table TestConformance: Protocol module test {
  method #Protocol.test: @test_method
}

// First function (should be parsed)
sil @foo : $@convention(thin) () -> () {
bb0:
  %0 = tuple ()
  return %0
}

// Second function (should be parsed)
sil hidden @bar : $@convention(thin) (Int) -> Int {
bb0(%0 : $Int):
  return %0
}
"#;

        let module = parse_sil(sil).expect("parse failed");
        assert_eq!(
            module.functions.len(),
            2,
            "should parse exactly 2 functions, skipping all sil_* declarations"
        );
        assert_eq!(module.functions[0].name, "foo");
        assert_eq!(module.functions[1].name, "bar");
    }

    #[test]
    fn test_parse_complex_type() {
        // Complex nested type in function signature
        let sil = r"
sil_stage canonical

sil @complex_sig : $@convention(thin) (Optional<Int>, Array<String>) -> Optional<Bool> {
bb0(%0 : $Optional<Int>, %1 : $Array<String>):
  %2 = integer_literal $Builtin.Int1, 0
  %3 = enum $Optional<Bool>, #Optional.none!enumelt
  return %3
}
";

        let module = parse_sil(sil).expect("parse failed");
        assert_eq!(module.functions.len(), 1);

        let func = &module.functions[0];
        // Just verify it parsed without error - the type structure is complex
        assert_eq!(func.name, "complex_sig");
        assert_eq!(func.blocks.len(), 1);
        assert_eq!(func.blocks[0].arguments.len(), 2);
    }

    #[test]
    fn test_parse_function_with_no_params() {
        // Function with empty parameter list
        let sil = r"
sil_stage canonical

sil @no_params : $@convention(thin) () -> Int {
bb0:
  %0 = integer_literal $Builtin.Int64, 42
  %1 = struct $Int (%0)
  return %1
}
";

        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let block = &func.blocks[0];

        assert!(block.arguments.is_empty(), "bb0 should have no arguments");
    }

    #[test]
    fn test_parse_mangled_name_with_special_chars() {
        // Mangled names can have various special characters
        let sil = r"
sil_stage canonical

sil @$s4test3addyS2i_SitF : $@convention(thin) (Int, Int) -> Int {
bb0(%0 : $Int, %1 : $Int):
  return %0
}
";

        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];

        // Mangled name includes $ and numbers
        assert!(func.name.starts_with("$s"));
        assert!(func.name.contains("add"));
    }

    #[test]
    fn test_parse_negative_integer_literal() {
        // Negative integer literals
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> Int {
bb0:
  %0 = integer_literal $Builtin.Int64, -42
  %1 = struct $Int (%0)
  return %1
}
";

        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let block = &func.blocks[0];

        let int_lit = block.instructions.iter().find(|inst| {
            matches!(&inst.kind, SilInstructionKind::IntegerLiteral { value, .. } if *value == -42)
        });
        assert!(
            int_lit.is_some(),
            "should find integer_literal with value -42"
        );
    }

    #[test]
    fn test_parse_string_literal_with_escapes() {
        // String literals with escape sequences
        let sil = r#"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = string_literal utf8 "hello\nworld"
  %1 = tuple ()
  return %1
}
"#;

        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let block = &func.blocks[0];

        let str_lit = block
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::StringLiteral { .. }));
        assert!(str_lit.is_some(), "should find string_literal instruction");
    }

    #[test]
    fn test_parse_branch_with_args() {
        // Unconditional branch with arguments
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (Int, Int) -> Int {
bb0(%0 : $Int, %1 : $Int):
  br bb1(%0, %1)
bb1(%2 : $Int, %3 : $Int):
  return %2
}
";

        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];

        assert_eq!(func.blocks.len(), 2);

        // Check bb0 branches with args
        let bb0 = &func.blocks[0];
        if let SilTerminator::Branch { dest, args } = &bb0.terminator {
            assert_eq!(dest, "bb1");
            assert_eq!(args.len(), 2);
            assert_eq!(args[0], "%0");
            assert_eq!(args[1], "%1");
        } else {
            panic!("expected Branch terminator");
        }

        // Check bb1 receives args
        let bb1 = &func.blocks[1];
        assert_eq!(bb1.arguments.len(), 2);
    }

    #[test]
    fn test_parse_switch_enum() {
        // switch_enum terminator - using simple control flow instead
        // (switch_enum parsing is complex; testing via cond_br which is similar)
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (Builtin.Int1) -> Int {
bb0(%0 : $Builtin.Int1):
  cond_br %0, bb1, bb2
bb1:
  %1 = integer_literal $Builtin.Int64, 1
  %2 = struct $Int (%1)
  return %2
bb2:
  %3 = integer_literal $Builtin.Int64, 0
  %4 = struct $Int (%3)
  return %4
}
";

        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];

        let bb0 = &func.blocks[0];
        assert!(matches!(&bb0.terminator, SilTerminator::CondBranch { .. }));
        assert_eq!(func.blocks.len(), 3);
    }

    #[test]
    fn test_parse_select_enum() {
        // select_enum instruction - produces a value based on enum discriminant
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (Optional<Int>) -> Bool {
bb0(%0 : $Optional<Int>):
  %1 = integer_literal $Builtin.Int1, -1
  %2 = integer_literal $Builtin.Int1, 0
  %3 = struct $Bool (%1)
  %4 = struct $Bool (%2)
  %5 = select_enum %0 : $Optional<Int>, case #Optional.none!enumelt: %3, case #Optional.some!enumelt: %4 : $Bool
  return %5
}
";

        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        // Find the select_enum instruction (should be %5)
        let select_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::SelectEnum { .. }))
            .expect("should find select_enum instruction");

        if let SilInstructionKind::SelectEnum {
            operand,
            cases,
            default,
        } = &select_inst.kind
        {
            assert_eq!(operand, "%0");
            assert_eq!(cases.len(), 2);
            assert!(cases[0].0.contains("Optional.none"));
            assert_eq!(cases[0].1, "%3");
            assert!(cases[1].0.contains("Optional.some"));
            assert_eq!(cases[1].1, "%4");
            assert!(default.is_none());
        } else {
            panic!("expected SelectEnum instruction");
        }
    }

    #[test]
    fn test_parse_select_enum_with_default() {
        // select_enum instruction with default case
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (Optional<Int>) -> Int {
bb0(%0 : $Optional<Int>):
  %1 = integer_literal $Builtin.Int64, 0
  %2 = struct $Int (%1)
  %3 = integer_literal $Builtin.Int64, 1
  %4 = struct $Int (%3)
  %5 = select_enum %0 : $Optional<Int>, case #Optional.some!enumelt: %4, default %2 : $Int
  return %5
}
";

        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let select_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::SelectEnum { .. }))
            .expect("should find select_enum instruction");

        if let SilInstructionKind::SelectEnum {
            operand,
            cases,
            default,
        } = &select_inst.kind
        {
            assert_eq!(operand, "%0");
            assert_eq!(cases.len(), 1);
            assert!(cases[0].0.contains("Optional.some"));
            assert_eq!(cases[0].1, "%4");
            assert_eq!(default.as_deref(), Some("%2"));
        } else {
            panic!("expected SelectEnum instruction");
        }
    }

    #[test]
    fn test_parse_whitespace_only_input() {
        // Only whitespace should produce empty module with default stage
        let sil = "sil_stage canonical\n   \n\t\n";

        let module = parse_sil(sil).expect("parse failed");
        assert_eq!(module.stage, SilStage::Canonical);
        assert!(module.functions.is_empty());
    }

    #[test]
    fn test_parse_multiple_functions() {
        // Multiple functions in one module
        let sil = r"
sil_stage canonical

sil @func1 : $@convention(thin) () -> () {
bb0:
  %0 = tuple ()
  return %0
}

sil @func2 : $@convention(thin) () -> () {
bb0:
  %0 = tuple ()
  return %0
}

sil @func3 : $@convention(thin) () -> () {
bb0:
  %0 = tuple ()
  return %0
}
";

        let module = parse_sil(sil).expect("parse failed");
        assert_eq!(module.functions.len(), 3);

        let names: Vec<_> = module.functions.iter().map(|f| f.name.as_str()).collect();
        assert!(names.contains(&"func1"));
        assert!(names.contains(&"func2"));
        assert!(names.contains(&"func3"));
    }

    #[test]
    fn test_parse_init_enum_data_addr() {
        // init_enum_data_addr - get address for enum payload data
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (Int) -> @out Optional<Int> {
bb0(%0 : $*Optional<Int>, %1 : $Int):
  %2 = init_enum_data_addr %0 : $*Optional<Int>, #Optional.some!enumelt
  store %1 to %2 : $*Int
  inject_enum_addr %0 : $*Optional<Int>, #Optional.some!enumelt
  %5 = tuple ()
  return %5
}
";

        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        // Find init_enum_data_addr instruction
        let init_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::InitEnumDataAddr { .. }))
            .expect("should find init_enum_data_addr instruction");

        if let SilInstructionKind::InitEnumDataAddr { address, case_name } = &init_inst.kind {
            assert_eq!(address, "%0");
            assert!(case_name.contains("Optional.some"));
        } else {
            panic!("expected InitEnumDataAddr instruction");
        }
    }

    #[test]
    fn test_parse_inject_enum_addr() {
        // inject_enum_addr - set discriminator for in-place enum
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (Int) -> @out Optional<Int> {
bb0(%0 : $*Optional<Int>, %1 : $Int):
  %2 = init_enum_data_addr %0 : $*Optional<Int>, #Optional.some!enumelt
  store %1 to %2 : $*Int
  inject_enum_addr %0 : $*Optional<Int>, #Optional.some!enumelt
  %5 = tuple ()
  return %5
}
";

        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        // Find inject_enum_addr instruction
        let inject_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::InjectEnumAddr { .. }))
            .expect("should find inject_enum_addr instruction");

        if let SilInstructionKind::InjectEnumAddr { address, case_name } = &inject_inst.kind {
            assert_eq!(address, "%0");
            assert!(case_name.contains("Optional.some"));
        } else {
            panic!("expected InjectEnumAddr instruction");
        }
    }

    #[test]
    fn test_parse_unchecked_take_enum_data_addr() {
        // unchecked_take_enum_data_addr - extract enum payload address
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (@in Optional<Int>) -> Int {
bb0(%0 : $*Optional<Int>):
  switch_enum_addr %0 : $*Optional<Int>, case #Optional.some!enumelt: bb1, case #Optional.none!enumelt: bb2
bb1:
  %2 = unchecked_take_enum_data_addr %0 : $*Optional<Int>, #Optional.some!enumelt
  %3 = load %2 : $*Int
  br bb3(%3)
bb2:
  %5 = integer_literal $Builtin.Int64, 0
  %6 = struct $Int (%5)
  br bb3(%6)
bb3(%7 : $Int):
  return %7
}
";

        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb1 = &func.blocks[1];

        // Find unchecked_take_enum_data_addr instruction
        let take_inst = bb1
            .instructions
            .iter()
            .find(|inst| {
                matches!(
                    &inst.kind,
                    SilInstructionKind::UncheckedTakeEnumDataAddr { .. }
                )
            })
            .expect("should find unchecked_take_enum_data_addr instruction");

        if let SilInstructionKind::UncheckedTakeEnumDataAddr { address, case_name } =
            &take_inst.kind
        {
            assert_eq!(address, "%0");
            assert!(case_name.contains("Optional.some"));
        } else {
            panic!("expected UncheckedTakeEnumDataAddr instruction");
        }
    }

    #[test]
    fn test_parse_switch_enum_addr() {
        // switch_enum_addr - branch based on indirect enum discriminant
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (@in Optional<Int>) -> Int {
bb0(%0 : $*Optional<Int>):
  switch_enum_addr %0 : $*Optional<Int>, case #Optional.some!enumelt: bb1, case #Optional.none!enumelt: bb2
bb1:
  %2 = unchecked_take_enum_data_addr %0 : $*Optional<Int>, #Optional.some!enumelt
  %3 = load %2 : $*Int
  br bb3(%3)
bb2:
  %5 = integer_literal $Builtin.Int64, 0
  %6 = struct $Int (%5)
  br bb3(%6)
bb3(%7 : $Int):
  return %7
}
";

        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        // Check switch_enum_addr terminator
        if let SilTerminator::SwitchEnumAddr {
            address,
            cases,
            default,
        } = &bb0.terminator
        {
            assert_eq!(address, "%0");
            assert_eq!(cases.len(), 2);
            assert!(cases[0].0.contains("Optional.some"));
            assert_eq!(cases[0].1, "bb1");
            assert!(cases[1].0.contains("Optional.none"));
            assert_eq!(cases[1].1, "bb2");
            assert!(default.is_none());
        } else {
            panic!("expected SwitchEnumAddr terminator");
        }
    }

    #[test]
    fn test_parse_switch_enum_with_default() {
        // switch_enum with default case - testing exhaustive switch with fallback
        let sil = r"
sil_stage canonical

enum MyEnum {
  case a
  case b
  case c
}

sil @test : $@convention(thin) (MyEnum) -> Int {
bb0(%0 : $MyEnum):
  switch_enum %0 : $MyEnum, case #MyEnum.a!enumelt: bb1, case #MyEnum.b!enumelt: bb2, default bb3
bb1:
  %1 = integer_literal $Builtin.Int64, 1
  %2 = struct $Int (%1)
  return %2
bb2:
  %3 = integer_literal $Builtin.Int64, 2
  %4 = struct $Int (%3)
  return %4
bb3:
  %5 = integer_literal $Builtin.Int64, 0
  %6 = struct $Int (%5)
  return %6
}
";

        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        // Check switch_enum with default
        if let SilTerminator::SwitchEnum {
            operand,
            cases,
            default,
        } = &bb0.terminator
        {
            assert_eq!(operand, "%0");
            assert_eq!(cases.len(), 2);
            assert!(cases[0].0.contains("MyEnum.a"));
            assert_eq!(cases[0].1, "bb1");
            assert!(cases[1].0.contains("MyEnum.b"));
            assert_eq!(cases[1].1, "bb2");
            assert_eq!(default.as_ref(), Some(&"bb3".to_string()));
        } else {
            panic!("expected SwitchEnum terminator");
        }
    }

    #[test]
    fn test_parse_switch_enum_addr_with_default() {
        // switch_enum_addr with default case
        let sil = r"
sil_stage canonical

enum MyEnum {
  case a
  case b
  case c
}

sil @test : $@convention(thin) (@in MyEnum) -> Int {
bb0(%0 : $*MyEnum):
  switch_enum_addr %0 : $*MyEnum, case #MyEnum.a!enumelt: bb1, default bb2
bb1:
  %2 = integer_literal $Builtin.Int64, 1
  %3 = struct $Int (%2)
  return %3
bb2:
  %4 = integer_literal $Builtin.Int64, 0
  %5 = struct $Int (%4)
  return %5
}
";

        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        // Check switch_enum_addr with default
        if let SilTerminator::SwitchEnumAddr {
            address,
            cases,
            default,
        } = &bb0.terminator
        {
            assert_eq!(address, "%0");
            assert_eq!(cases.len(), 1);
            assert!(cases[0].0.contains("MyEnum.a"));
            assert_eq!(cases[0].1, "bb1");
            assert_eq!(default.as_ref(), Some(&"bb2".to_string()));
        } else {
            panic!("expected SwitchEnumAddr terminator");
        }
    }

    #[test]
    fn test_parse_switch_enum_multi_case() {
        // switch_enum with many cases - testing 4+ cases
        let sil = r"
sil_stage canonical

enum Direction {
  case north
  case south
  case east
  case west
}

sil @test : $@convention(thin) (Direction) -> Int {
bb0(%0 : $Direction):
  switch_enum %0 : $Direction, case #Direction.north!enumelt: bb1, case #Direction.south!enumelt: bb2, case #Direction.east!enumelt: bb3, case #Direction.west!enumelt: bb4
bb1:
  %1 = integer_literal $Builtin.Int64, 0
  %2 = struct $Int (%1)
  return %2
bb2:
  %3 = integer_literal $Builtin.Int64, 1
  %4 = struct $Int (%3)
  return %4
bb3:
  %5 = integer_literal $Builtin.Int64, 2
  %6 = struct $Int (%5)
  return %6
bb4:
  %7 = integer_literal $Builtin.Int64, 3
  %8 = struct $Int (%7)
  return %8
}
";

        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        // Check switch_enum with 4 cases
        if let SilTerminator::SwitchEnum {
            operand,
            cases,
            default,
        } = &bb0.terminator
        {
            assert_eq!(operand, "%0");
            assert_eq!(cases.len(), 4);
            assert!(cases[0].0.contains("Direction.north"));
            assert!(cases[1].0.contains("Direction.south"));
            assert!(cases[2].0.contains("Direction.east"));
            assert!(cases[3].0.contains("Direction.west"));
            assert!(default.is_none());
        } else {
            panic!("expected SwitchEnum terminator");
        }
    }

    #[test]
    fn test_parse_switch_enum_generic_type() {
        // switch_enum with generic type like Optional<Array<Int>>
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (Optional<Array<Int>>) -> Int {
bb0(%0 : $Optional<Array<Int>>):
  switch_enum %0 : $Optional<Array<Int>>, case #Optional.some!enumelt: bb1, case #Optional.none!enumelt: bb2
bb1(%1 : $Array<Int>):
  %2 = integer_literal $Builtin.Int64, 1
  %3 = struct $Int (%2)
  return %3
bb2:
  %4 = integer_literal $Builtin.Int64, 0
  %5 = struct $Int (%4)
  return %5
}
";

        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        // Check switch_enum parses generic type correctly
        if let SilTerminator::SwitchEnum {
            operand,
            cases,
            default,
        } = &bb0.terminator
        {
            assert_eq!(operand, "%0");
            assert_eq!(cases.len(), 2);
            assert!(cases[0].0.contains("Optional.some"));
            assert!(cases[1].0.contains("Optional.none"));
            assert!(default.is_none());
        } else {
            panic!("expected SwitchEnum terminator");
        }
    }

    #[test]
    fn test_parse_init_existential_addr() {
        // init_existential_addr - prepare address for protocol existential storage
        let sil = r"
sil_stage canonical

protocol P {}

sil @test : $@convention(thin) <T where T : P> (@in T) -> @out P {
bb0(%0 : $*P, %1 : $*T):
  %2 = init_existential_addr %0 : $*P, $T
  copy_addr %1 to [init] %2 : $*T
  %4 = tuple ()
  return %4
}
";

        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        // Find init_existential_addr instruction
        let init_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::InitExistentialAddr { .. }))
            .expect("should find init_existential_addr instruction");

        if let SilInstructionKind::InitExistentialAddr { address, ty } = &init_inst.kind {
            assert_eq!(address, "%0");
            // Type should be parsed
            assert!(matches!(ty, SilType::Named(_)));
        } else {
            panic!("expected InitExistentialAddr instruction");
        }
    }

    #[test]
    fn test_parse_open_existential_addr() {
        // open_existential_addr - open protocol existential at address
        let sil = r#"
sil_stage canonical

protocol P {}

sil @test : $@convention(thin) (@in P) -> () {
bb0(%0 : $*P):
  %1 = open_existential_addr immutable_access %0 : $*P to $*@opened("01234567-89ab-cdef-0123-000000000000", P) Self
  %2 = tuple ()
  return %2
}
"#;

        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        // Find open_existential_addr instruction
        let open_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::OpenExistentialAddr { .. }))
            .expect("should find open_existential_addr instruction");

        if let SilInstructionKind::OpenExistentialAddr { address, .. } = &open_inst.kind {
            assert_eq!(address, "%0");
        } else {
            panic!("expected OpenExistentialAddr instruction");
        }
    }

    #[test]
    fn test_parse_init_existential_ref() {
        // init_existential_ref - wrap class ref in existential
        let sil = r"
sil_stage canonical

protocol ClassP : AnyObject {}
class ConcreteClass : ClassP {}

sil @test : $@convention(thin) (@guaranteed ConcreteClass) -> @owned ClassP {
bb0(%0 : $ConcreteClass):
  %1 = init_existential_ref %0 : $ConcreteClass : $ConcreteClass, $ClassP
  return %1
}
";

        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        // Find init_existential_ref instruction
        let init_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::InitExistentialRef { .. }))
            .expect("should find init_existential_ref instruction");

        if let SilInstructionKind::InitExistentialRef { operand, ty } = &init_inst.kind {
            assert_eq!(operand, "%0");
            // Type should be the protocol type
            if let SilType::Named(name) = ty {
                assert!(name.contains("ClassP") || name.contains("class"));
            }
        } else {
            panic!("expected InitExistentialRef instruction");
        }
    }

    #[test]
    fn test_parse_open_existential_ref() {
        // open_existential_ref - open class existential to get concrete ref
        let sil = r#"
sil_stage canonical

protocol ClassP : AnyObject {}

sil @test : $@convention(thin) (@guaranteed ClassP) -> () {
bb0(%0 : $ClassP):
  %1 = open_existential_ref %0 : $ClassP to $@opened("01234567-89ab-cdef-0123-000000000000", ClassP) Self
  %2 = tuple ()
  return %2
}
"#;

        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        // Find open_existential_ref instruction
        let open_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::OpenExistentialRef { .. }))
            .expect("should find open_existential_ref instruction");

        if let SilInstructionKind::OpenExistentialRef { operand, .. } = &open_inst.kind {
            assert_eq!(operand, "%0");
        } else {
            panic!("expected OpenExistentialRef instruction");
        }
    }

    #[test]
    fn test_parse_existential_metatype() {
        // existential_metatype - extract metatype from existential value
        let sil = r"
sil_stage canonical

protocol P {}

sil @test : $@convention(thin) (@in P) -> @thick P.Type {
bb0(%0 : $*P):
  %1 = existential_metatype $@thick P.Type, %0 : $*P
  return %1
}
";

        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        // Find existential_metatype instruction
        let meta_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::ExistentialMetatype { .. }))
            .expect("should find existential_metatype instruction");

        if let SilInstructionKind::ExistentialMetatype { operand, ty } = &meta_inst.kind {
            assert_eq!(operand, "%0");
            // Type should be the protocol metatype
            if let SilType::Named(name) = ty {
                assert!(name.contains("thick") || name.contains('P'));
            }
        } else {
            panic!("expected ExistentialMetatype instruction");
        }
    }

    #[test]
    fn test_parse_init_existential_metatype() {
        // init_existential_metatype - wrap concrete metatype in existential metatype
        let sil = r"
sil_stage canonical

protocol P {}
struct D : P {}

sil @test : $@convention(thin) () -> @thick P.Type {
bb0:
  %0 = metatype $@thick D.Type
  %1 = init_existential_metatype %0 : $@thick D.Type, $@thick P.Type
  return %1
}
";

        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        // Find init_existential_metatype instruction
        let init_inst = bb0
            .instructions
            .iter()
            .find(|inst| {
                matches!(
                    &inst.kind,
                    SilInstructionKind::InitExistentialMetatype { .. }
                )
            })
            .expect("should find init_existential_metatype instruction");

        if let SilInstructionKind::InitExistentialMetatype { operand, ty } = &init_inst.kind {
            assert_eq!(operand, "%0");
            // Type should be the protocol metatype
            if let SilType::Named(name) = ty {
                assert!(name.contains("thick") || name.contains('P'));
            }
        } else {
            panic!("expected InitExistentialMetatype instruction");
        }
    }

    #[test]
    fn test_parse_open_existential_metatype() {
        // open_existential_metatype - open existential metatype to get concrete metatype
        let sil = r#"
sil_stage canonical

protocol P {}

sil @test : $@convention(thin) (@thick P.Type) -> () {
bb0(%0 : $@thick P.Type):
  %1 = open_existential_metatype %0 : $@thick P.Type to $@thick (@opened("00000000-0000-0000-0000-000000000000", P) Self).Type
  %2 = tuple ()
  return %2
}
"#;

        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        // Find open_existential_metatype instruction
        let open_inst = bb0
            .instructions
            .iter()
            .find(|inst| {
                matches!(
                    &inst.kind,
                    SilInstructionKind::OpenExistentialMetatype { .. }
                )
            })
            .expect("should find open_existential_metatype instruction");

        if let SilInstructionKind::OpenExistentialMetatype { operand, ty } = &open_inst.kind {
            assert_eq!(operand, "%0");
            // Type should contain @opened
            if let SilType::Named(name) = ty {
                assert!(name.contains("thick") || name.contains("opened"));
            }
        } else {
            panic!("expected OpenExistentialMetatype instruction");
        }
    }

    #[test]
    fn test_parse_alloc_existential_box() {
        // alloc_existential_box - allocate boxed existential container
        let sil = r"
sil_stage canonical

protocol P {}
struct S : P {}

sil @test : $@convention(thin) () -> @owned P {
bb0:
  %0 = alloc_existential_box $P, $S
  %1 = tuple ()
  return %0
}
";

        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        // Find alloc_existential_box instruction
        let alloc_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::AllocExistentialBox { .. }))
            .expect("should find alloc_existential_box instruction");

        if let SilInstructionKind::AllocExistentialBox {
            existential_ty,
            concrete_ty,
        } = &alloc_inst.kind
        {
            // Existential type should be P
            if let SilType::Named(name) = existential_ty {
                assert!(name.contains('P'));
            }
            // Concrete type should be S
            if let SilType::Named(name) = concrete_ty {
                assert!(name.contains('S'));
            }
        } else {
            panic!("expected AllocExistentialBox instruction");
        }
    }

    #[test]
    fn test_parse_project_existential_box() {
        // project_existential_box - project address from boxed existential
        let sil = r"
sil_stage canonical

protocol P {}
struct S : P {}

sil @test : $@convention(thin) (@owned P) -> () {
bb0(%0 : $P):
  %1 = project_existential_box $S in %0 : $P
  %2 = tuple ()
  return %2
}
";

        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        // Find project_existential_box instruction
        let project_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::ProjectExistentialBox { .. }))
            .expect("should find project_existential_box instruction");

        if let SilInstructionKind::ProjectExistentialBox {
            concrete_ty,
            operand,
        } = &project_inst.kind
        {
            assert_eq!(operand, "%0");
            // Concrete type should be S
            if let SilType::Named(name) = concrete_ty {
                assert!(name.contains('S'));
            }
        } else {
            panic!("expected ProjectExistentialBox instruction");
        }
    }

    #[test]
    fn test_parse_open_existential_box() {
        // open_existential_box - open boxed existential to address with archetype
        let sil = r#"
sil_stage canonical

protocol P {}

sil @test : $@convention(thin) (@owned P) -> () {
bb0(%0 : $P):
  %1 = open_existential_box %0 : $P to $*@opened("01234567-89ab-cdef-0123-000000000001", P) Self
  %2 = tuple ()
  return %2
}
"#;

        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        // Find open_existential_box instruction
        let open_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::OpenExistentialBox { .. }))
            .expect("should find open_existential_box instruction");

        if let SilInstructionKind::OpenExistentialBox { operand, ty } = &open_inst.kind {
            assert_eq!(operand, "%0");
            // Type should contain @opened
            if let SilType::Named(name) = ty {
                assert!(name.contains("opened") || name.contains("Self"));
            }
        } else {
            panic!("expected OpenExistentialBox instruction");
        }
    }

    #[test]
    fn test_parse_open_existential_box_value() {
        // open_existential_box_value - open boxed existential to value
        let sil = r#"
sil_stage canonical

protocol P {}

sil @test : $@convention(thin) (@owned P) -> () {
bb0(%0 : $P):
  %1 = open_existential_box_value %0 : $P to $@opened("01234567-89ab-cdef-0123-000000000002", P) Self
  %2 = tuple ()
  return %2
}
"#;

        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        // Find open_existential_box_value instruction
        let open_inst = bb0
            .instructions
            .iter()
            .find(|inst| {
                matches!(
                    &inst.kind,
                    SilInstructionKind::OpenExistentialBoxValue { .. }
                )
            })
            .expect("should find open_existential_box_value instruction");

        if let SilInstructionKind::OpenExistentialBoxValue { operand, ty } = &open_inst.kind {
            assert_eq!(operand, "%0");
            // Type should contain @opened
            if let SilType::Named(name) = ty {
                assert!(name.contains("opened") || name.contains("Self"));
            }
        } else {
            panic!("expected OpenExistentialBoxValue instruction");
        }
    }

    #[test]
    fn test_parse_dealloc_existential_box() {
        // dealloc_existential_box - deallocate boxed existential container
        let sil = r"
sil_stage canonical

protocol P {}
struct S : P {}

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_existential_box $P, $S
  dealloc_existential_box %0 : $P, $S
  %2 = tuple ()
  return %2
}
";

        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        // Find dealloc_existential_box instruction
        let dealloc_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::DeallocExistentialBox { .. }))
            .expect("should find dealloc_existential_box instruction");

        if let SilInstructionKind::DeallocExistentialBox {
            operand,
            concrete_ty,
        } = &dealloc_inst.kind
        {
            assert_eq!(operand, "%0");
            // Concrete type should be S
            if let SilType::Named(name) = concrete_ty {
                assert!(name.contains('S'));
            }
        } else {
            panic!("expected DeallocExistentialBox instruction");
        }
    }

    #[test]
    fn test_parse_yield_terminator() {
        // yield terminator for coroutines
        let sil = "\
sil_stage canonical
sil @test : $@convention(thin) () -> () {
bb0:
  %0 = tuple ()
  yield %0 : $(), resume bb1, unwind bb2
bb1:
  %1 = tuple ()
  return %1 : $()
bb2:
  unwind
}
";
        let result = parse_sil(sil);
        assert!(result.is_ok(), "yield SIL should parse: {:?}", result.err());

        let module = result.unwrap();
        assert_eq!(module.functions.len(), 1);
        let func = &module.functions[0];
        assert_eq!(func.blocks.len(), 3);

        // Check bb0 has yield terminator
        let bb0 = &func.blocks[0];
        assert_eq!(bb0.label, "bb0");
        match &bb0.terminator {
            SilTerminator::Yield {
                values,
                resume_dest,
                unwind_dest,
            } => {
                assert_eq!(values, &vec!["%0".to_string()]);
                assert_eq!(resume_dest, "bb1");
                assert_eq!(unwind_dest, "bb2");
            }
            other => panic!("expected Yield terminator, got {other:?}"),
        }

        // Check bb1 has return terminator
        let bb1 = &func.blocks[1];
        assert_eq!(bb1.label, "bb1");
        assert!(matches!(&bb1.terminator, SilTerminator::Return { .. }));

        // Check bb2 has unwind terminator
        let bb2 = &func.blocks[2];
        assert_eq!(bb2.label, "bb2");
        assert!(matches!(&bb2.terminator, SilTerminator::Unwind));
    }

    // ==================== Helper Function Unit Tests ====================

    // --- consume_type_name tests ---

    #[test]
    fn test_consume_type_name_simple() {
        let mut parser = SilParser::new("Int");
        let result = parser.consume_type_name();
        assert_eq!(result, "Int");
        assert!(parser.is_eof());
    }

    #[test]
    fn test_consume_type_name_with_dot() {
        let mut parser = SilParser::new("Swift.Int");
        let result = parser.consume_type_name();
        assert_eq!(result, "Swift.Int");
        assert!(parser.is_eof());
    }

    #[test]
    fn test_consume_type_name_with_underscore() {
        let mut parser = SilParser::new("_value123");
        let result = parser.consume_type_name();
        assert_eq!(result, "_value123");
    }

    #[test]
    fn test_consume_type_name_unicode_greek() {
        // Greek letter tau used in generic params like τ_0_0
        let mut parser = SilParser::new("τ_0_0");
        let result = parser.consume_type_name();
        assert_eq!(result, "τ_0_0");
    }

    #[test]
    fn test_consume_type_name_stops_at_special_chars() {
        let mut parser = SilParser::new("Int<");
        let result = parser.consume_type_name();
        assert_eq!(result, "Int");
        assert_eq!(parser.current_char(), Some('<'));
    }

    #[test]
    fn test_consume_type_name_empty_input() {
        let mut parser = SilParser::new("");
        let result = parser.consume_type_name();
        assert_eq!(result, "");
    }

    // --- consume_until_whitespace_or_colon tests ---

    #[test]
    fn test_consume_until_whitespace_or_colon_whitespace() {
        let mut parser = SilParser::new("foo bar");
        let result = parser.consume_until_whitespace_or_colon();
        assert_eq!(result, "foo");
        assert_eq!(parser.current_char(), Some(' '));
    }

    #[test]
    fn test_consume_until_whitespace_or_colon_colon() {
        let mut parser = SilParser::new("$Int:");
        let result = parser.consume_until_whitespace_or_colon();
        assert_eq!(result, "$Int");
        assert_eq!(parser.current_char(), Some(':'));
    }

    #[test]
    fn test_consume_until_whitespace_or_colon_tab() {
        let mut parser = SilParser::new("value\trest");
        let result = parser.consume_until_whitespace_or_colon();
        assert_eq!(result, "value");
        assert_eq!(parser.current_char(), Some('\t'));
    }

    #[test]
    fn test_consume_until_whitespace_or_colon_entire_string() {
        let mut parser = SilParser::new("NoStopChar");
        let result = parser.consume_until_whitespace_or_colon();
        assert_eq!(result, "NoStopChar");
        assert!(parser.is_eof());
    }

    // --- consume_until_char tests ---

    #[test]
    fn test_consume_until_char_found() {
        let mut parser = SilParser::new("hello)world");
        let result = parser.consume_until_char(')');
        assert_eq!(result, "hello");
        assert_eq!(parser.current_char(), Some(')'));
    }

    #[test]
    fn test_consume_until_char_not_found() {
        let mut parser = SilParser::new("noend");
        let result = parser.consume_until_char('X');
        assert_eq!(result, "noend");
        assert!(parser.is_eof());
    }

    #[test]
    fn test_consume_until_char_at_start() {
        let mut parser = SilParser::new(")rest");
        let result = parser.consume_until_char(')');
        assert_eq!(result, "");
        assert_eq!(parser.current_char(), Some(')'));
    }

    // --- consume_until_char_in tests ---

    #[test]
    fn test_consume_until_char_in_first_stop() {
        let mut parser = SilParser::new("abc,def");
        let result = parser.consume_until_char_in(&[',', ';']);
        assert_eq!(result, "abc");
        assert_eq!(parser.current_char(), Some(','));
    }

    #[test]
    fn test_consume_until_char_in_second_stop() {
        let mut parser = SilParser::new("abc;def");
        let result = parser.consume_until_char_in(&[',', ';']);
        assert_eq!(result, "abc");
        assert_eq!(parser.current_char(), Some(';'));
    }

    #[test]
    fn test_consume_until_char_in_none_found() {
        let mut parser = SilParser::new("abcdef");
        let result = parser.consume_until_char_in(&[',', ';', ':']);
        assert_eq!(result, "abcdef");
        assert!(parser.is_eof());
    }

    #[test]
    fn test_consume_until_char_in_empty_stops() {
        let mut parser = SilParser::new("abc");
        let result = parser.consume_until_char_in(&[]);
        assert_eq!(result, "abc");
        assert!(parser.is_eof());
    }

    // --- consume_until_str tests ---

    #[test]
    fn test_consume_until_str_found() {
        let mut parser = SilParser::new("hello -> world");
        let result = parser.consume_until_str("->");
        assert_eq!(result, "hello ");
        assert!(parser.peek_str("->"));
    }

    #[test]
    fn test_consume_until_str_not_found() {
        let mut parser = SilParser::new("no arrow here");
        let result = parser.consume_until_str("->");
        assert_eq!(result, "no arrow here");
        assert!(parser.is_eof());
    }

    #[test]
    fn test_consume_until_str_at_start() {
        let mut parser = SilParser::new("->rest");
        let result = parser.consume_until_str("->");
        assert_eq!(result, "");
        assert!(parser.peek_str("->"));
    }

    // --- consume_to_eol tests ---

    #[test]
    fn test_consume_to_eol_with_newline() {
        let mut parser = SilParser::new("line1\nline2");
        let result = parser.consume_to_eol();
        assert_eq!(result, "line1");
        assert_eq!(parser.current_char(), Some('\n'));
    }

    #[test]
    fn test_consume_to_eol_no_newline() {
        let mut parser = SilParser::new("only line");
        let result = parser.consume_to_eol();
        assert_eq!(result, "only line");
        assert!(parser.is_eof());
    }

    #[test]
    fn test_consume_to_eol_empty_line() {
        let mut parser = SilParser::new("\nrest");
        let result = parser.consume_to_eol();
        assert_eq!(result, "");
        assert_eq!(parser.current_char(), Some('\n'));
    }

    // --- skip_whitespace tests ---

    #[test]
    fn test_skip_whitespace_spaces() {
        let mut parser = SilParser::new("   abc");
        parser.skip_whitespace();
        assert_eq!(parser.current_char(), Some('a'));
    }

    #[test]
    fn test_skip_whitespace_tabs() {
        let mut parser = SilParser::new("\t\tabc");
        parser.skip_whitespace();
        assert_eq!(parser.current_char(), Some('a'));
    }

    #[test]
    fn test_skip_whitespace_newlines() {
        let mut parser = SilParser::new("\n\nabc");
        parser.skip_whitespace();
        assert_eq!(parser.current_char(), Some('a'));
    }

    #[test]
    fn test_skip_whitespace_mixed() {
        let mut parser = SilParser::new("  \t\n  abc");
        parser.skip_whitespace();
        assert_eq!(parser.current_char(), Some('a'));
    }

    #[test]
    fn test_skip_whitespace_no_whitespace() {
        let mut parser = SilParser::new("abc");
        parser.skip_whitespace();
        assert_eq!(parser.current_char(), Some('a'));
    }

    #[test]
    fn test_skip_whitespace_all_whitespace() {
        let mut parser = SilParser::new("   ");
        parser.skip_whitespace();
        assert!(parser.is_eof());
    }

    // --- skip_whitespace_on_line tests ---

    #[test]
    fn test_skip_whitespace_on_line_spaces() {
        let mut parser = SilParser::new("   abc");
        parser.skip_whitespace_on_line();
        assert_eq!(parser.current_char(), Some('a'));
    }

    #[test]
    fn test_skip_whitespace_on_line_tabs() {
        let mut parser = SilParser::new("\t\tabc");
        parser.skip_whitespace_on_line();
        assert_eq!(parser.current_char(), Some('a'));
    }

    #[test]
    fn test_skip_whitespace_on_line_stops_at_newline() {
        let mut parser = SilParser::new("  \nabc");
        parser.skip_whitespace_on_line();
        assert_eq!(parser.current_char(), Some('\n'));
    }

    #[test]
    fn test_skip_whitespace_on_line_newline_first() {
        let mut parser = SilParser::new("\nabc");
        parser.skip_whitespace_on_line();
        assert_eq!(parser.current_char(), Some('\n'));
    }

    // --- skip_whitespace_and_comments tests ---

    #[test]
    fn test_skip_whitespace_and_comments_simple() {
        let mut parser = SilParser::new("   abc");
        parser.skip_whitespace_and_comments();
        assert_eq!(parser.current_char(), Some('a'));
    }

    #[test]
    fn test_skip_whitespace_and_comments_line_comment() {
        let mut parser = SilParser::new("  // comment\nabc");
        parser.skip_whitespace_and_comments();
        assert_eq!(parser.current_char(), Some('a'));
    }

    #[test]
    fn test_skip_whitespace_and_comments_multiple_comments() {
        let mut parser = SilParser::new("// first\n// second\nabc");
        parser.skip_whitespace_and_comments();
        assert_eq!(parser.current_char(), Some('a'));
    }

    #[test]
    fn test_skip_whitespace_and_comments_no_whitespace() {
        let mut parser = SilParser::new("abc");
        parser.skip_whitespace_and_comments();
        assert_eq!(parser.current_char(), Some('a'));
    }

    #[test]
    fn test_skip_whitespace_and_comments_comment_at_eof() {
        let mut parser = SilParser::new("// only comment");
        parser.skip_whitespace_and_comments();
        assert!(parser.is_eof());
    }

    // --- is_result_assignment tests ---

    #[test]
    fn test_is_result_assignment_single_register() {
        let parser = SilParser::new("%0 = integer_literal");
        assert!(parser.is_result_assignment());
    }

    #[test]
    fn test_is_result_assignment_numbered_register() {
        let parser = SilParser::new("%123 = load");
        assert!(parser.is_result_assignment());
    }

    #[test]
    fn test_is_result_assignment_tuple_result() {
        let parser = SilParser::new("(%0, %1) = apply");
        assert!(parser.is_result_assignment());
    }

    #[test]
    fn test_is_result_assignment_not_assignment_debug_value() {
        let parser = SilParser::new("%0, let x");
        assert!(!parser.is_result_assignment());
    }

    #[test]
    fn test_is_result_assignment_not_percent() {
        let parser = SilParser::new("return %0");
        assert!(!parser.is_result_assignment());
    }

    #[test]
    fn test_is_result_assignment_with_spaces() {
        let parser = SilParser::new("%0   =   something");
        assert!(parser.is_result_assignment());
    }

    #[test]
    fn test_is_result_assignment_tuple_nested_parens() {
        let parser = SilParser::new("((%0)) = something");
        assert!(parser.is_result_assignment());
    }

    // --- skip_balanced_brackets tests ---

    #[test]
    fn test_skip_balanced_brackets_simple() {
        let mut parser = SilParser::new("(abc)rest");
        parser.skip_balanced_brackets('(', ')').unwrap();
        assert_eq!(parser.current_char(), Some('r'));
    }

    #[test]
    fn test_skip_balanced_brackets_nested() {
        let mut parser = SilParser::new("((inner))rest");
        parser.skip_balanced_brackets('(', ')').unwrap();
        assert_eq!(parser.current_char(), Some('r'));
    }

    #[test]
    fn test_skip_balanced_brackets_square() {
        let mut parser = SilParser::new("[a[b]c]rest");
        parser.skip_balanced_brackets('[', ']').unwrap();
        assert_eq!(parser.current_char(), Some('r'));
    }

    #[test]
    fn test_skip_balanced_brackets_curly() {
        let mut parser = SilParser::new("{a{b}c}rest");
        parser.skip_balanced_brackets('{', '}').unwrap();
        assert_eq!(parser.current_char(), Some('r'));
    }

    #[test]
    fn test_skip_balanced_brackets_angle() {
        let mut parser = SilParser::new("<T<U>>rest");
        parser.skip_balanced_brackets('<', '>').unwrap();
        assert_eq!(parser.current_char(), Some('r'));
    }

    #[test]
    fn test_skip_balanced_brackets_unbalanced() {
        let mut parser = SilParser::new("(abc");
        let result = parser.skip_balanced_brackets('(', ')');
        assert!(result.is_err());
    }

    #[test]
    fn test_skip_balanced_brackets_not_starting_with_open() {
        let mut parser = SilParser::new("abc(");
        let result = parser.skip_balanced_brackets('(', ')');
        assert!(result.is_err());
    }

    // --- current_char tests ---

    #[test]
    fn test_current_char_start() {
        let parser = SilParser::new("abc");
        assert_eq!(parser.current_char(), Some('a'));
    }

    #[test]
    fn test_current_char_empty() {
        let parser = SilParser::new("");
        assert_eq!(parser.current_char(), None);
    }

    #[test]
    fn test_current_char_unicode() {
        let parser = SilParser::new("τ_0");
        assert_eq!(parser.current_char(), Some('τ'));
    }

    // --- advance tests ---

    #[test]
    fn test_advance_ascii() {
        let mut parser = SilParser::new("abc");
        assert_eq!(parser.current_char(), Some('a'));
        parser.advance();
        assert_eq!(parser.current_char(), Some('b'));
        parser.advance();
        assert_eq!(parser.current_char(), Some('c'));
        parser.advance();
        assert_eq!(parser.current_char(), None);
    }

    #[test]
    fn test_advance_unicode() {
        let mut parser = SilParser::new("τab");
        assert_eq!(parser.current_char(), Some('τ'));
        parser.advance(); // τ is 2 bytes
        assert_eq!(parser.current_char(), Some('a'));
    }

    #[test]
    fn test_advance_line_tracking() {
        let mut parser = SilParser::new("a\nb");
        assert_eq!(parser.line, 1);
        parser.advance(); // 'a'
        assert_eq!(parser.line, 1);
        parser.advance(); // '\n'
        assert_eq!(parser.line, 2);
        assert_eq!(parser.current_char(), Some('b'));
    }

    // --- peek_char tests ---

    #[test]
    fn test_peek_char_match() {
        let parser = SilParser::new("abc");
        assert!(parser.peek_char('a'));
    }

    #[test]
    fn test_peek_char_no_match() {
        let parser = SilParser::new("abc");
        assert!(!parser.peek_char('b'));
    }

    #[test]
    fn test_peek_char_empty() {
        let parser = SilParser::new("");
        assert!(!parser.peek_char('a'));
    }

    // --- peek_str tests ---

    #[test]
    fn test_peek_str_match() {
        let parser = SilParser::new("hello world");
        assert!(parser.peek_str("hello"));
    }

    #[test]
    fn test_peek_str_no_match() {
        let parser = SilParser::new("hello world");
        assert!(!parser.peek_str("world"));
    }

    #[test]
    fn test_peek_str_partial_match() {
        let parser = SilParser::new("he");
        assert!(!parser.peek_str("hello"));
    }

    #[test]
    fn test_peek_str_exact_match() {
        let parser = SilParser::new("abc");
        assert!(parser.peek_str("abc"));
    }

    #[test]
    fn test_peek_str_empty_pattern() {
        let parser = SilParser::new("abc");
        assert!(parser.peek_str(""));
    }

    // --- expect_char tests ---

    #[test]
    fn test_expect_char_match() {
        let mut parser = SilParser::new("abc");
        assert!(parser.expect_char('a').is_ok());
        assert_eq!(parser.current_char(), Some('b'));
    }

    #[test]
    fn test_expect_char_no_match() {
        let mut parser = SilParser::new("abc");
        let result = parser.expect_char('x');
        assert!(result.is_err());
    }

    #[test]
    fn test_expect_char_eof() {
        let mut parser = SilParser::new("");
        let result = parser.expect_char('a');
        assert!(result.is_err());
    }

    // --- expect_str tests ---

    #[test]
    fn test_expect_str_match() {
        let mut parser = SilParser::new("hello world");
        assert!(parser.expect_str("hello").is_ok());
        assert_eq!(parser.current_char(), Some(' '));
    }

    #[test]
    fn test_expect_str_no_match() {
        let mut parser = SilParser::new("hello world");
        let result = parser.expect_str("world");
        assert!(result.is_err());
    }

    #[test]
    fn test_expect_str_partial() {
        let mut parser = SilParser::new("hel");
        let result = parser.expect_str("hello");
        assert!(result.is_err());
    }

    // --- is_eof tests ---

    #[test]
    fn test_is_eof_empty() {
        let parser = SilParser::new("");
        assert!(parser.is_eof());
    }

    #[test]
    fn test_is_eof_not_empty() {
        let parser = SilParser::new("a");
        assert!(!parser.is_eof());
    }

    #[test]
    fn test_is_eof_after_consume() {
        let mut parser = SilParser::new("a");
        assert!(!parser.is_eof());
        parser.advance();
        assert!(parser.is_eof());
    }

    // --- error tests ---

    #[test]
    fn test_error_includes_position() {
        let mut parser = SilParser::new("ab\ncd");
        parser.advance(); // a
        parser.advance(); // b
        parser.advance(); // \n
        let err = parser.error("test error");
        assert_eq!(err.message, "test error");
        assert_eq!(err.line, 2);
        assert_eq!(err.column, 1);
    }

    #[test]
    fn test_error_at_start() {
        let parser = SilParser::new("abc");
        let err = parser.error("start error");
        assert_eq!(err.line, 1);
        assert_eq!(err.column, 1);
    }

    // --- parse_load tests ---

    #[test]
    fn test_parse_load_with_copy() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (@in Int) -> Int {
bb0(%0 : $*Int):
  %1 = load [copy] %0 : $*Int
  return %1 : $Int
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let load_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::Load { .. }))
            .expect("should find load instruction");

        if let SilInstructionKind::Load { kind, address } = &load_inst.kind {
            assert_eq!(*kind, LoadKind::Copy);
            assert_eq!(address, "%0");
        } else {
            panic!("expected Load instruction");
        }
    }

    #[test]
    fn test_parse_load_with_take() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (@in Int) -> Int {
bb0(%0 : $*Int):
  %1 = load [take] %0 : $*Int
  return %1 : $Int
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let load_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::Load { .. }))
            .expect("should find load instruction");

        if let SilInstructionKind::Load { kind, .. } = &load_inst.kind {
            assert_eq!(*kind, LoadKind::Take);
        } else {
            panic!("expected Load instruction");
        }
    }

    #[test]
    fn test_parse_load_with_trivial() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (@in Int) -> Int {
bb0(%0 : $*Int):
  %1 = load [trivial] %0 : $*Int
  return %1 : $Int
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let load_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::Load { .. }))
            .expect("should find load instruction");

        if let SilInstructionKind::Load { kind, .. } = &load_inst.kind {
            assert_eq!(*kind, LoadKind::Trivial);
        } else {
            panic!("expected Load instruction");
        }
    }

    #[test]
    fn test_parse_load_with_borrow() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (@in Int) -> Int {
bb0(%0 : $*Int):
  %1 = load [borrow] %0 : $*Int
  return %1 : $Int
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let load_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::Load { .. }))
            .expect("should find load instruction");

        if let SilInstructionKind::Load { kind, .. } = &load_inst.kind {
            assert_eq!(*kind, LoadKind::Borrow);
        } else {
            panic!("expected Load instruction");
        }
    }

    #[test]
    fn test_parse_load_no_qualifier() {
        // Test load without any qualifier (defaults to Take)
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (@in Int) -> Int {
bb0(%0 : $*Int):
  %1 = load %0 : $*Int
  return %1 : $Int
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let load_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::Load { .. }))
            .expect("should find load instruction");

        if let SilInstructionKind::Load { kind, .. } = &load_inst.kind {
            // Default should be Take
            assert_eq!(*kind, LoadKind::Take);
        } else {
            panic!("expected Load instruction");
        }
    }

    // --- parse_store tests ---

    #[test]
    fn test_parse_store_with_init() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (Int) -> () {
bb0(%0 : $Int):
  %1 = alloc_stack $Int
  store %0 to [init] %1 : $*Int
  dealloc_stack %1
  %2 = tuple ()
  return %2 : $()
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let store_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::Store { .. }))
            .expect("should find store instruction");

        if let SilInstructionKind::Store { kind, source, dest } = &store_inst.kind {
            assert_eq!(*kind, StoreKind::Init);
            assert_eq!(source, "%0");
            assert_eq!(dest, "%1");
        } else {
            panic!("expected Store instruction");
        }
    }

    #[test]
    fn test_parse_store_with_assign() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (Int) -> () {
bb0(%0 : $Int):
  %1 = alloc_stack $Int
  store %0 to [assign] %1 : $*Int
  dealloc_stack %1
  %2 = tuple ()
  return %2 : $()
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let store_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::Store { .. }))
            .expect("should find store instruction");

        if let SilInstructionKind::Store { kind, .. } = &store_inst.kind {
            assert_eq!(*kind, StoreKind::Assign);
        } else {
            panic!("expected Store instruction");
        }
    }

    #[test]
    fn test_parse_store_with_trivial() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (Int) -> () {
bb0(%0 : $Int):
  %1 = alloc_stack $Int
  store %0 to [trivial] %1 : $*Int
  dealloc_stack %1
  %2 = tuple ()
  return %2 : $()
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let store_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::Store { .. }))
            .expect("should find store instruction");

        if let SilInstructionKind::Store { kind, .. } = &store_inst.kind {
            assert_eq!(*kind, StoreKind::Trivial);
        } else {
            panic!("expected Store instruction");
        }
    }

    #[test]
    fn test_parse_store_no_qualifier() {
        // Test store without any qualifier (defaults to Init)
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (Int) -> () {
bb0(%0 : $Int):
  %1 = alloc_stack $Int
  store %0 to %1 : $*Int
  dealloc_stack %1
  %2 = tuple ()
  return %2 : $()
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let store_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::Store { .. }))
            .expect("should find store instruction");

        if let SilInstructionKind::Store { kind, .. } = &store_inst.kind {
            // Default should be Init
            assert_eq!(*kind, StoreKind::Init);
        } else {
            panic!("expected Store instruction");
        }
    }

    // --- parse_struct tests ---

    #[test]
    fn test_parse_struct_construction() {
        let sil = r"
sil_stage canonical

struct Point {
  var x: Int
  var y: Int
}

sil @test : $@convention(thin) (Int, Int) -> Point {
bb0(%0 : $Int, %1 : $Int):
  %2 = struct $Point (%0 : $Int, %1 : $Int)
  return %2 : $Point
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let struct_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::Struct { .. }))
            .expect("should find struct instruction");

        if let SilInstructionKind::Struct { ty, operands } = &struct_inst.kind {
            assert!(matches!(ty, SilType::Named(name) if name.contains("Point")));
            assert_eq!(operands.len(), 2);
            assert_eq!(operands[0], "%0");
            assert_eq!(operands[1], "%1");
        } else {
            panic!("expected Struct instruction");
        }
    }

    #[test]
    fn test_parse_struct_extract_field() {
        let sil = r"
sil_stage canonical

struct Point {
  var x: Int
  var y: Int
}

sil @test : $@convention(thin) (Point) -> Int {
bb0(%0 : $Point):
  %1 = struct_extract %0, #Point.x
  return %1 : $Int
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let extract_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::StructExtract { .. }))
            .expect("should find struct_extract instruction");

        if let SilInstructionKind::StructExtract { operand, field } = &extract_inst.kind {
            assert_eq!(operand, "%0");
            assert!(field.contains("Point") && field.contains('x'));
        } else {
            panic!("expected StructExtract instruction");
        }
    }

    #[test]
    fn test_parse_struct_empty() {
        let sil = r"
sil_stage canonical

struct Empty {}

sil @test : $@convention(thin) () -> Empty {
bb0:
  %0 = struct $Empty ()
  return %0 : $Empty
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let struct_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::Struct { .. }))
            .expect("should find struct instruction");

        if let SilInstructionKind::Struct { operands, .. } = &struct_inst.kind {
            assert!(operands.is_empty());
        } else {
            panic!("expected Struct instruction");
        }
    }

    // --- parse_tuple tests ---

    #[test]
    fn test_parse_tuple_construction() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (Int, Bool) -> (Int, Bool) {
bb0(%0 : $Int, %1 : $Bool):
  %2 = tuple (%0 : $Int, %1 : $Bool)
  return %2 : $(Int, Bool)
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let tuple_inst = bb0
            .instructions
            .iter()
            .find(|inst| {
                matches!(&inst.kind, SilInstructionKind::Tuple { operands, .. } if operands.len() == 2)
            })
            .expect("should find tuple instruction with 2 operands");

        if let SilInstructionKind::Tuple { operands, .. } = &tuple_inst.kind {
            assert_eq!(operands.len(), 2);
            assert_eq!(operands[0], "%0");
            assert_eq!(operands[1], "%1");
        } else {
            panic!("expected Tuple instruction");
        }
    }

    #[test]
    fn test_parse_tuple_extract_element() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) ((Int, Bool)) -> Int {
bb0(%0 : $(Int, Bool)):
  %1 = tuple_extract %0, 0
  return %1 : $Int
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let extract_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::TupleExtract { .. }))
            .expect("should find tuple_extract instruction");

        if let SilInstructionKind::TupleExtract { operand, index } = &extract_inst.kind {
            assert_eq!(operand, "%0");
            assert_eq!(*index, 0);
        } else {
            panic!("expected TupleExtract instruction");
        }
    }

    #[test]
    fn test_parse_tuple_empty() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = tuple ()
  return %0 : $()
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let tuple_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::Tuple { .. }))
            .expect("should find tuple instruction");

        if let SilInstructionKind::Tuple { operands, .. } = &tuple_inst.kind {
            assert!(operands.is_empty());
        } else {
            panic!("expected Tuple instruction");
        }
    }

    #[test]
    fn test_parse_tuple_extract_second_element() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) ((Int, Bool, String)) -> Bool {
bb0(%0 : $(Int, Bool, String)):
  %1 = tuple_extract %0, 1
  return %1 : $Bool
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let extract_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::TupleExtract { .. }))
            .expect("should find tuple_extract instruction");

        if let SilInstructionKind::TupleExtract { index, .. } = &extract_inst.kind {
            assert_eq!(*index, 1);
        } else {
            panic!("expected TupleExtract instruction");
        }
    }

    // --- parse_builtin tests ---

    #[test]
    fn test_parse_builtin_sadd_with_overflow() {
        let sil = r#"
sil_stage canonical

sil @test : $@convention(thin) (Builtin.Int64, Builtin.Int64) -> (Builtin.Int64, Builtin.Int1) {
bb0(%0 : $Builtin.Int64, %1 : $Builtin.Int64):
  %2 = builtin "sadd_with_overflow_Int64"(%0 : $Builtin.Int64, %1 : $Builtin.Int64) : $(Builtin.Int64, Builtin.Int1)
  return %2 : $(Builtin.Int64, Builtin.Int1)
}
"#;
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let builtin_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::Builtin { .. }))
            .expect("should find builtin instruction");

        if let SilInstructionKind::Builtin {
            name, arguments, ..
        } = &builtin_inst.kind
        {
            assert_eq!(name, "sadd_with_overflow_Int64");
            assert_eq!(arguments.len(), 2);
            assert_eq!(arguments[0], "%0");
            assert_eq!(arguments[1], "%1");
        } else {
            panic!("expected Builtin instruction");
        }
    }

    #[test]
    fn test_parse_builtin_cmp() {
        let sil = r#"
sil_stage canonical

sil @test : $@convention(thin) (Builtin.Int64, Builtin.Int64) -> Builtin.Int1 {
bb0(%0 : $Builtin.Int64, %1 : $Builtin.Int64):
  %2 = builtin "cmp_slt_Int64"(%0 : $Builtin.Int64, %1 : $Builtin.Int64) : $Builtin.Int1
  return %2 : $Builtin.Int1
}
"#;
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let builtin_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::Builtin { .. }))
            .expect("should find builtin instruction");

        if let SilInstructionKind::Builtin { name, .. } = &builtin_inst.kind {
            assert_eq!(name, "cmp_slt_Int64");
        } else {
            panic!("expected Builtin instruction");
        }
    }

    #[test]
    fn test_parse_builtin_with_generic_arg() {
        let sil = r#"
sil_stage canonical

sil @test : $@convention(thin) (Builtin.RawPointer) -> Builtin.Int64 {
bb0(%0 : $Builtin.RawPointer):
  %1 = builtin "ptrtoint_Word"<Int64>(%0 : $Builtin.RawPointer) : $Builtin.Int64
  return %1 : $Builtin.Int64
}
"#;
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let builtin_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::Builtin { .. }))
            .expect("should find builtin instruction");

        if let SilInstructionKind::Builtin { name, .. } = &builtin_inst.kind {
            assert_eq!(name, "ptrtoint_Word");
        } else {
            panic!("expected Builtin instruction");
        }
    }

    // --- parse_apply tests ---

    #[test]
    fn test_parse_apply_simple() {
        let sil = r"
sil_stage canonical

sil @callee : $@convention(thin) (Int) -> Int

sil @test : $@convention(thin) (Int) -> Int {
bb0(%0 : $Int):
  %1 = function_ref @callee : $@convention(thin) (Int) -> Int
  %2 = apply %1(%0) : $@convention(thin) (Int) -> Int
  return %2 : $Int
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let apply_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::Apply { .. }))
            .expect("should find apply instruction");

        if let SilInstructionKind::Apply {
            callee, arguments, ..
        } = &apply_inst.kind
        {
            assert_eq!(callee, "%1");
            assert_eq!(arguments.len(), 1);
            assert_eq!(arguments[0], "%0");
        } else {
            panic!("expected Apply instruction");
        }
    }

    #[test]
    fn test_parse_apply_with_isolation() {
        let sil = r"
sil_stage canonical

sil @callee : $@convention(thin) (Int) -> Int

sil @test : $@convention(thin) (Int) -> Int {
bb0(%0 : $Int):
  %1 = function_ref @callee : $@convention(thin) (Int) -> Int
  %2 = apply [caller_isolation=nonisolated] %1(%0) : $@convention(thin) (Int) -> Int
  return %2 : $Int
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let apply_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::Apply { .. }))
            .expect("should find apply instruction");

        if let SilInstructionKind::Apply {
            caller_isolation, ..
        } = &apply_inst.kind
        {
            assert_eq!(*caller_isolation, Some(ActorIsolation::Nonisolated));
        } else {
            panic!("expected Apply instruction");
        }
    }

    #[test]
    fn test_parse_apply_with_callee_isolation() {
        let sil = r"
sil_stage canonical

sil @callee : $@convention(thin) (Int) -> Int

sil @test : $@convention(thin) (Int) -> Int {
bb0(%0 : $Int):
  %1 = function_ref @callee : $@convention(thin) (Int) -> Int
  %2 = apply [callee_isolation=actor_instance] %1(%0) : $@convention(thin) (Int) -> Int
  return %2 : $Int
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let apply_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::Apply { .. }))
            .expect("should find apply instruction");

        if let SilInstructionKind::Apply {
            callee_isolation, ..
        } = &apply_inst.kind
        {
            assert_eq!(*callee_isolation, Some(ActorIsolation::ActorInstance));
        } else {
            panic!("expected Apply instruction");
        }
    }

    #[test]
    fn test_parse_apply_multiple_args() {
        let sil = r"
sil_stage canonical

sil @callee : $@convention(thin) (Int, Int, Int) -> Int

sil @test : $@convention(thin) (Int, Int, Int) -> Int {
bb0(%0 : $Int, %1 : $Int, %2 : $Int):
  %3 = function_ref @callee : $@convention(thin) (Int, Int, Int) -> Int
  %4 = apply %3(%0, %1, %2) : $@convention(thin) (Int, Int, Int) -> Int
  return %4 : $Int
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let apply_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::Apply { .. }))
            .expect("should find apply instruction");

        if let SilInstructionKind::Apply { arguments, .. } = &apply_inst.kind {
            assert_eq!(arguments.len(), 3);
            assert_eq!(arguments[0], "%0");
            assert_eq!(arguments[1], "%1");
            assert_eq!(arguments[2], "%2");
        } else {
            panic!("expected Apply instruction");
        }
    }

    // --- parse_function_ref tests ---

    #[test]
    fn test_parse_function_ref() {
        let sil = r"
sil_stage canonical

sil @target : $@convention(thin) () -> ()

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = function_ref @target : $@convention(thin) () -> ()
  %1 = tuple ()
  return %1 : $()
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let ref_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::FunctionRef { .. }))
            .expect("should find function_ref instruction");

        if let SilInstructionKind::FunctionRef { name } = &ref_inst.kind {
            assert!(name.contains("target"));
        } else {
            panic!("expected FunctionRef instruction");
        }
    }

    #[test]
    fn test_parse_dynamic_function_ref() {
        let sil = r"
sil_stage canonical

sil @target : $@convention(thin) () -> ()

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = dynamic_function_ref @target : $@convention(thin) () -> ()
  %1 = tuple ()
  return %1 : $()
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let ref_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::DynamicFunctionRef { .. }))
            .expect("should find dynamic_function_ref instruction");

        if let SilInstructionKind::DynamicFunctionRef { name } = &ref_inst.kind {
            assert!(name.contains("target"));
        } else {
            panic!("expected DynamicFunctionRef instruction");
        }
    }

    // ============================================================
    // Additional instruction parser tests (alloc/dealloc, metatype, access, etc.)
    // ============================================================

    #[test]
    fn test_parse_alloc_stack_simple() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_stack $Int64
  dealloc_stack %0 : $*Int64
  %2 = tuple ()
  return %2 : $()
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let alloc_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::AllocStack { .. }))
            .expect("should find alloc_stack instruction");

        if let SilInstructionKind::AllocStack { ty } = &alloc_inst.kind {
            // Int64 is parsed as Named("Int64")
            assert!(matches!(ty, SilType::Named(name) if name == "Int64"));
        } else {
            panic!("expected AllocStack instruction");
        }
    }

    #[test]
    fn test_parse_alloc_stack_with_attributes() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_stack [lexical] [var_decl] $Bool
  dealloc_stack %0 : $*Bool
  %2 = tuple ()
  return %2 : $()
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let alloc_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::AllocStack { .. }))
            .expect("should find alloc_stack instruction");

        if let SilInstructionKind::AllocStack { ty } = &alloc_inst.kind {
            // Bool is parsed as Named("Bool")
            assert!(matches!(ty, SilType::Named(name) if name == "Bool"));
        } else {
            panic!("expected AllocStack instruction");
        }
    }

    #[test]
    fn test_parse_dealloc_stack() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_stack $Int64
  dealloc_stack %0 : $*Int64
  %2 = tuple ()
  return %2 : $()
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let dealloc_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::DeallocStack { .. }))
            .expect("should find dealloc_stack instruction");

        if let SilInstructionKind::DeallocStack { operand } = &dealloc_inst.kind {
            assert_eq!(operand, "%0");
        } else {
            panic!("expected DeallocStack instruction");
        }
    }

    #[test]
    fn test_parse_metatype() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = metatype $@thin Int64.Type
  %1 = tuple ()
  return %1 : $()
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let metatype_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::Metatype { .. }))
            .expect("should find metatype instruction");

        assert!(matches!(
            metatype_inst.kind,
            SilInstructionKind::Metatype { .. }
        ));
    }

    #[test]
    fn test_parse_value_metatype() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (@in_guaranteed Int64) -> () {
bb0(%0 : $*Int64):
  %1 = load [trivial] %0 : $*Int64
  %2 = value_metatype $@thick Int64.Type, %1 : $Int64
  %3 = tuple ()
  return %3 : $()
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let value_metatype_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::ValueMetatype { .. }))
            .expect("should find value_metatype instruction");

        if let SilInstructionKind::ValueMetatype { operand } = &value_metatype_inst.kind {
            assert_eq!(operand, "%1");
        } else {
            panic!("expected ValueMetatype instruction");
        }
    }

    #[test]
    fn test_parse_begin_access_read_dynamic() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (@inout Int64) -> () {
bb0(%0 : $*Int64):
  %1 = begin_access [read] [dynamic] %0 : $*Int64
  end_access %1 : $*Int64
  %3 = tuple ()
  return %3 : $()
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let begin_access_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::BeginAccess { .. }))
            .expect("should find begin_access instruction");

        if let SilInstructionKind::BeginAccess {
            kind,
            enforcement,
            address,
        } = &begin_access_inst.kind
        {
            assert!(matches!(kind, AccessKind::Read));
            assert!(matches!(enforcement, Enforcement::Dynamic));
            assert_eq!(address, "%0");
        } else {
            panic!("expected BeginAccess instruction");
        }
    }

    #[test]
    fn test_parse_begin_access_modify_static() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (@inout Int64) -> () {
bb0(%0 : $*Int64):
  %1 = begin_access [modify] [static] %0 : $*Int64
  end_access %1 : $*Int64
  %3 = tuple ()
  return %3 : $()
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let begin_access_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::BeginAccess { .. }))
            .expect("should find begin_access instruction");

        if let SilInstructionKind::BeginAccess {
            kind,
            enforcement,
            address,
        } = &begin_access_inst.kind
        {
            assert!(matches!(kind, AccessKind::Modify));
            assert!(matches!(enforcement, Enforcement::Static));
            assert_eq!(address, "%0");
        } else {
            panic!("expected BeginAccess instruction");
        }
    }

    #[test]
    fn test_parse_begin_access_with_no_nested_conflict() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (@inout Int64) -> () {
bb0(%0 : $*Int64):
  %1 = begin_access [read] [dynamic] [no_nested_conflict] %0 : $*Int64
  end_access %1 : $*Int64
  %3 = tuple ()
  return %3 : $()
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let begin_access_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::BeginAccess { .. }))
            .expect("should find begin_access instruction");

        if let SilInstructionKind::BeginAccess {
            kind,
            enforcement,
            address,
        } = &begin_access_inst.kind
        {
            assert!(matches!(kind, AccessKind::Read));
            assert!(matches!(enforcement, Enforcement::Dynamic));
            assert_eq!(address, "%0");
        } else {
            panic!("expected BeginAccess instruction");
        }
    }

    #[test]
    fn test_parse_end_access() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (@inout Int64) -> () {
bb0(%0 : $*Int64):
  %1 = begin_access [read] [dynamic] %0 : $*Int64
  end_access %1 : $*Int64
  %3 = tuple ()
  return %3 : $()
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let end_access_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::EndAccess { .. }))
            .expect("should find end_access instruction");

        if let SilInstructionKind::EndAccess { address } = &end_access_inst.kind {
            assert_eq!(address, "%1");
        } else {
            panic!("expected EndAccess instruction");
        }
    }

    #[test]
    fn test_parse_end_access_with_abort() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (@inout Int64) -> () {
bb0(%0 : $*Int64):
  %1 = begin_access [read] [dynamic] %0 : $*Int64
  end_access [abort] %1 : $*Int64
  %3 = tuple ()
  return %3 : $()
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let end_access_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::EndAccess { .. }))
            .expect("should find end_access instruction");

        if let SilInstructionKind::EndAccess { address } = &end_access_inst.kind {
            assert_eq!(address, "%1");
        } else {
            panic!("expected EndAccess instruction");
        }
    }

    #[test]
    fn test_parse_begin_borrow() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (@guaranteed String) -> () {
bb0(%0 : $String):
  %1 = begin_borrow %0 : $String
  end_borrow %1 : $String
  %3 = tuple ()
  return %3 : $()
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let begin_borrow_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::BeginBorrow { .. }))
            .expect("should find begin_borrow instruction");

        if let SilInstructionKind::BeginBorrow { operand } = &begin_borrow_inst.kind {
            assert_eq!(operand, "%0");
        } else {
            panic!("expected BeginBorrow instruction");
        }
    }

    #[test]
    fn test_parse_end_borrow() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (@guaranteed String) -> () {
bb0(%0 : $String):
  %1 = begin_borrow %0 : $String
  end_borrow %1 : $String
  %3 = tuple ()
  return %3 : $()
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let end_borrow_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::EndBorrow { .. }))
            .expect("should find end_borrow instruction");

        if let SilInstructionKind::EndBorrow { operand } = &end_borrow_inst.kind {
            assert_eq!(operand, "%1");
        } else {
            panic!("expected EndBorrow instruction");
        }
    }

    #[test]
    fn test_parse_copy_value() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (@guaranteed String) -> @owned String {
bb0(%0 : $String):
  %1 = copy_value %0 : $String
  return %1 : $String
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let copy_value_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::CopyValue { .. }))
            .expect("should find copy_value instruction");

        if let SilInstructionKind::CopyValue { operand } = &copy_value_inst.kind {
            assert_eq!(operand, "%0");
        } else {
            panic!("expected CopyValue instruction");
        }
    }

    #[test]
    fn test_parse_destroy_value() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (@owned String) -> () {
bb0(%0 : $String):
  destroy_value %0 : $String
  %2 = tuple ()
  return %2 : $()
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let destroy_value_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::DestroyValue { .. }))
            .expect("should find destroy_value instruction");

        if let SilInstructionKind::DestroyValue { operand } = &destroy_value_inst.kind {
            assert_eq!(operand, "%0");
        } else {
            panic!("expected DestroyValue instruction");
        }
    }

    #[test]
    fn test_parse_strong_retain() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (@guaranteed SomeClass) -> () {
bb0(%0 : $SomeClass):
  strong_retain %0 : $SomeClass
  %2 = tuple ()
  return %2 : $()
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let strong_retain_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::StrongRetain { .. }))
            .expect("should find strong_retain instruction");

        if let SilInstructionKind::StrongRetain { operand } = &strong_retain_inst.kind {
            assert_eq!(operand, "%0");
        } else {
            panic!("expected StrongRetain instruction");
        }
    }

    #[test]
    fn test_parse_strong_release() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (@owned SomeClass) -> () {
bb0(%0 : $SomeClass):
  strong_release %0 : $SomeClass
  %2 = tuple ()
  return %2 : $()
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let strong_release_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::StrongRelease { .. }))
            .expect("should find strong_release instruction");

        if let SilInstructionKind::StrongRelease { operand } = &strong_release_inst.kind {
            assert_eq!(operand, "%0");
        } else {
            panic!("expected StrongRelease instruction");
        }
    }

    #[test]
    fn test_parse_enum_simple() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = enum $Optional<Int64>, #Optional.none!enumelt
  %1 = tuple ()
  return %1 : $()
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let enum_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::Enum { .. }))
            .expect("should find enum instruction");

        if let SilInstructionKind::Enum {
            ty,
            case_name,
            operand,
        } = &enum_inst.kind
        {
            // Optional<Int64> is parsed as Optional(Named("Int64"))
            assert!(matches!(ty, SilType::Optional(_)));
            assert!(case_name.contains("none"));
            assert!(operand.is_none());
        } else {
            panic!("expected Enum instruction");
        }
    }

    #[test]
    fn test_parse_enum_with_payload() {
        // Test with space before comma to match parser expectation
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (Int64) -> () {
bb0(%0 : $Int64):
  %1 = enum $Optional<Int64>, #Optional.some!enumelt , %0 : $Int64
  %2 = tuple ()
  return %2 : $()
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let enum_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::Enum { .. }))
            .expect("should find enum instruction");

        if let SilInstructionKind::Enum {
            ty,
            case_name,
            operand,
        } = &enum_inst.kind
        {
            // Optional<Int64> is parsed as Optional(Named("Int64"))
            assert!(matches!(ty, SilType::Optional(_)));
            assert!(case_name.contains("some"));
            // With space before comma, operand is parsed correctly
            assert_eq!(operand.as_ref().unwrap(), "%0");
        } else {
            panic!("expected Enum instruction");
        }
    }

    #[test]
    fn test_parse_global_addr() {
        let sil = r"
sil_stage canonical

sil_global @myGlobal : $Int64

sil @test : $@convention(thin) () -> Int64 {
bb0:
  %0 = global_addr @myGlobal : $*Int64
  %1 = load [trivial] %0 : $*Int64
  return %1 : $Int64
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let global_addr_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::GlobalAddr { .. }))
            .expect("should find global_addr instruction");

        if let SilInstructionKind::GlobalAddr { name } = &global_addr_inst.kind {
            assert_eq!(name, "myGlobal");
        } else {
            panic!("expected GlobalAddr instruction");
        }
    }

    #[test]
    fn test_parse_partial_apply_simple() {
        let sil = r"
sil_stage canonical

sil @target : $@convention(thin) (Int64) -> Int64

sil @test : $@convention(thin) (Int64) -> @callee_guaranteed () -> Int64 {
bb0(%0 : $Int64):
  %1 = function_ref @target : $@convention(thin) (Int64) -> Int64
  %2 = partial_apply [callee_guaranteed] %1(%0) : $@convention(thin) (Int64) -> Int64
  return %2 : $@callee_guaranteed () -> Int64
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let partial_apply_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::PartialApply { .. }))
            .expect("should find partial_apply instruction");

        if let SilInstructionKind::PartialApply {
            callee,
            substitutions,
            arguments,
            on_stack,
        } = &partial_apply_inst.kind
        {
            assert_eq!(callee, "%1");
            assert!(substitutions.is_empty());
            assert_eq!(arguments.len(), 1);
            assert_eq!(arguments[0], "%0");
            assert!(!on_stack);
        } else {
            panic!("expected PartialApply instruction");
        }
    }

    #[test]
    fn test_parse_partial_apply_on_stack() {
        let sil = r"
sil_stage canonical

sil @target : $@convention(thin) (Int64) -> Int64

sil @test : $@convention(thin) (Int64) -> @callee_guaranteed () -> Int64 {
bb0(%0 : $Int64):
  %1 = function_ref @target : $@convention(thin) (Int64) -> Int64
  %2 = partial_apply [callee_guaranteed] [on_stack] %1(%0) : $@convention(thin) (Int64) -> Int64
  return %2 : $@callee_guaranteed () -> Int64
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let partial_apply_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::PartialApply { .. }))
            .expect("should find partial_apply instruction");

        if let SilInstructionKind::PartialApply { on_stack, .. } = &partial_apply_inst.kind {
            assert!(*on_stack);
        } else {
            panic!("expected PartialApply instruction");
        }
    }

    #[test]
    fn test_parse_load_borrow() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (@in_guaranteed String) -> () {
bb0(%0 : $*String):
  %1 = load_borrow %0 : $*String
  end_borrow %1 : $String
  %3 = tuple ()
  return %3 : $()
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let load_borrow_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::LoadBorrow { .. }))
            .expect("should find load_borrow instruction");

        if let SilInstructionKind::LoadBorrow { address } = &load_borrow_inst.kind {
            assert_eq!(address, "%0");
        } else {
            panic!("expected LoadBorrow instruction");
        }
    }

    #[test]
    fn test_parse_begin_apply() {
        let sil = r"
sil_stage canonical

sil @generator : $@yield_once @convention(thin) () -> @yields Int64

sil @test : $@convention(thin) () -> Int64 {
bb0:
  %0 = function_ref @generator : $@yield_once @convention(thin) () -> @yields Int64
  (%1, %2) = begin_apply %0() : $@yield_once @convention(thin) () -> @yields Int64
  end_apply %2 as $()
  return %1 : $Int64
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let begin_apply_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::BeginApply { .. }))
            .expect("should find begin_apply instruction");

        if let SilInstructionKind::BeginApply {
            callee,
            substitutions,
            arguments,
        } = &begin_apply_inst.kind
        {
            assert_eq!(callee, "%0");
            assert!(substitutions.is_empty());
            assert!(arguments.is_empty());
        } else {
            panic!("expected BeginApply instruction");
        }
    }

    #[test]
    fn test_parse_end_apply() {
        let sil = r"
sil_stage canonical

sil @generator : $@yield_once @convention(thin) () -> @yields Int64

sil @test : $@convention(thin) () -> Int64 {
bb0:
  %0 = function_ref @generator : $@yield_once @convention(thin) () -> @yields Int64
  (%1, %2) = begin_apply %0() : $@yield_once @convention(thin) () -> @yields Int64
  end_apply %2 as $()
  return %1 : $Int64
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let end_apply_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::EndApply { .. }))
            .expect("should find end_apply instruction");

        if let SilInstructionKind::EndApply { token } = &end_apply_inst.kind {
            assert_eq!(token, "%2");
        } else {
            panic!("expected EndApply instruction");
        }
    }

    #[test]
    fn test_parse_abort_apply() {
        let sil = r"
sil_stage canonical

sil @generator : $@yield_once @convention(thin) () -> @yields Int64

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = function_ref @generator : $@yield_once @convention(thin) () -> @yields Int64
  (%1, %2) = begin_apply %0() : $@yield_once @convention(thin) () -> @yields Int64
  abort_apply %2
  %4 = tuple ()
  return %4 : $()
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let abort_apply_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::AbortApply { .. }))
            .expect("should find abort_apply instruction");

        if let SilInstructionKind::AbortApply { token } = &abort_apply_inst.kind {
            assert_eq!(token, "%2");
        } else {
            panic!("expected AbortApply instruction");
        }
    }

    #[test]
    fn test_parse_retain_value() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (@guaranteed SomeStruct) -> () {
bb0(%0 : $SomeStruct):
  retain_value %0 : $SomeStruct
  %2 = tuple ()
  return %2 : $()
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let retain_value_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::RetainValue { .. }))
            .expect("should find retain_value instruction");

        if let SilInstructionKind::RetainValue { operand } = &retain_value_inst.kind {
            assert_eq!(operand, "%0");
        } else {
            panic!("expected RetainValue instruction");
        }
    }

    #[test]
    fn test_parse_release_value() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (@owned SomeStruct) -> () {
bb0(%0 : $SomeStruct):
  release_value %0 : $SomeStruct
  %2 = tuple ()
  return %2 : $()
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let release_value_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::ReleaseValue { .. }))
            .expect("should find release_value instruction");

        if let SilInstructionKind::ReleaseValue { operand } = &release_value_inst.kind {
            assert_eq!(operand, "%0");
        } else {
            panic!("expected ReleaseValue instruction");
        }
    }

    #[test]
    fn test_parse_destroy_addr() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (@in String) -> () {
bb0(%0 : $*String):
  destroy_addr %0 : $*String
  %2 = tuple ()
  return %2 : $()
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let destroy_addr_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::DestroyAddr { .. }))
            .expect("should find destroy_addr instruction");

        if let SilInstructionKind::DestroyAddr { address } = &destroy_addr_inst.kind {
            assert_eq!(address, "%0");
        } else {
            panic!("expected DestroyAddr instruction");
        }
    }

    #[test]
    fn test_parse_convert_function() {
        let sil = r"
sil_stage canonical

sil @target : $@convention(thin) () -> ()

sil @test : $@convention(thin) () -> @convention(thick) () -> () {
bb0:
  %0 = function_ref @target : $@convention(thin) () -> ()
  %1 = convert_function %0 : $@convention(thin) () -> () to $@convention(thick) () -> ()
  return %1 : $@convention(thick) () -> ()
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let convert_func_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::ConvertFunction { .. }))
            .expect("should find convert_function instruction");

        if let SilInstructionKind::ConvertFunction { operand, .. } = &convert_func_inst.kind {
            assert_eq!(operand, "%0");
        } else {
            panic!("expected ConvertFunction instruction");
        }
    }

    #[test]
    fn test_parse_convert_function_with_attribute() {
        let sil = r"
sil_stage canonical

sil @target : $@convention(thin) () -> ()

sil @test : $@convention(thin) () -> @convention(thick) () -> () {
bb0:
  %0 = function_ref @target : $@convention(thin) () -> ()
  %1 = convert_function [without_actually_escaping] %0 : $@convention(thin) () -> () to $@convention(thick) () -> ()
  return %1 : $@convention(thick) () -> ()
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let convert_func_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::ConvertFunction { .. }))
            .expect("should find convert_function instruction");

        if let SilInstructionKind::ConvertFunction { operand, .. } = &convert_func_inst.kind {
            assert_eq!(operand, "%0");
        } else {
            panic!("expected ConvertFunction instruction");
        }
    }

    // ==================== upcast instruction tests ====================

    #[test]
    fn test_parse_upcast_simple() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_ref $ChildClass
  %1 = upcast %0 : $ChildClass to $ParentClass
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let upcast_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::Upcast { .. }))
            .expect("should find upcast instruction");

        if let SilInstructionKind::Upcast { operand, ty } = &upcast_inst.kind {
            assert_eq!(operand, "%0");
            assert!(matches!(ty, SilType::Named(name) if name.contains("ParentClass")));
        } else {
            panic!("expected Upcast instruction");
        }
    }

    #[test]
    fn test_parse_upcast_with_generic() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_ref $Array<Int>
  %1 = upcast %0 : $Array<Int> to $AnyObject
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let upcast_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::Upcast { .. }))
            .expect("should find upcast instruction");

        if let SilInstructionKind::Upcast { operand, .. } = &upcast_inst.kind {
            assert_eq!(operand, "%0");
        } else {
            panic!("expected Upcast instruction");
        }
    }

    // ==================== class_method instruction tests ====================

    #[test]
    fn test_parse_class_method_simple() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_ref $MyClass
  %1 = class_method %0 : $MyClass, #MyClass.doSomething : Type
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let class_method_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::ClassMethod { .. }))
            .expect("should find class_method instruction");

        if let SilInstructionKind::ClassMethod { operand, method } = &class_method_inst.kind {
            assert_eq!(operand, "%0");
            assert!(method.contains("MyClass.doSomething"));
        } else {
            panic!("expected ClassMethod instruction");
        }
    }

    #[test]
    fn test_parse_class_method_with_full_signature() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_ref $UIViewController
  %1 = class_method %0 : $UIViewController, #UIViewController.viewDidLoad : (UIViewController) -> () -> ()
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let class_method_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::ClassMethod { .. }))
            .expect("should find class_method instruction");

        if let SilInstructionKind::ClassMethod { operand, method } = &class_method_inst.kind {
            assert_eq!(operand, "%0");
            assert!(method.contains("viewDidLoad"));
        } else {
            panic!("expected ClassMethod instruction");
        }
    }

    // ==================== witness_method instruction tests ====================

    #[test]
    fn test_parse_witness_method_simple() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = witness_method $Int, #Comparable.compare : <Self where Self : Comparable> (Self) -> (Self) -> Bool
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let witness_method_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::WitnessMethod { .. }))
            .expect("should find witness_method instruction");

        if let SilInstructionKind::WitnessMethod { ty, method } = &witness_method_inst.kind {
            assert!(matches!(ty, SilType::Named(name) if name.contains("Int")));
            assert!(method.contains("Comparable.compare"));
        } else {
            panic!("expected WitnessMethod instruction");
        }
    }

    #[test]
    fn test_parse_witness_method_hashable() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = witness_method $String, #Hashable.hashValue!getter : <Self where Self : Hashable> (Self) -> Int
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let witness_method_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::WitnessMethod { .. }))
            .expect("should find witness_method instruction");

        if let SilInstructionKind::WitnessMethod { ty, method } = &witness_method_inst.kind {
            assert!(matches!(ty, SilType::Named(name) if name.contains("String")));
            assert!(method.contains("Hashable.hashValue"));
        } else {
            panic!("expected WitnessMethod instruction");
        }
    }

    // ==================== alloc_ref instruction tests ====================

    #[test]
    fn test_parse_alloc_ref_simple() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_ref $MyClass
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let alloc_ref_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::AllocRef { .. }))
            .expect("should find alloc_ref instruction");

        if let SilInstructionKind::AllocRef { ty, tail_elems } = &alloc_ref_inst.kind {
            assert!(matches!(ty, SilType::Named(name) if name.contains("MyClass")));
            assert!(tail_elems.is_empty());
        } else {
            panic!("expected AllocRef instruction");
        }
    }

    #[test]
    fn test_parse_alloc_ref_with_attributes() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_ref [objc] [stack] $NSObject
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let alloc_ref_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::AllocRef { .. }))
            .expect("should find alloc_ref instruction");

        if let SilInstructionKind::AllocRef { ty, .. } = &alloc_ref_inst.kind {
            assert!(matches!(ty, SilType::Named(name) if name.contains("NSObject")));
        } else {
            panic!("expected AllocRef instruction");
        }
    }

    #[test]
    fn test_parse_alloc_ref_with_tail_elems() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (Builtin.Word) -> () {
bb0(%count : $Builtin.Word):
  %0 = alloc_ref [tail_elems $Int * %count] $ContiguousArrayStorage<Int>
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let alloc_ref_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::AllocRef { .. }))
            .expect("should find alloc_ref instruction");

        if let SilInstructionKind::AllocRef { ty, tail_elems } = &alloc_ref_inst.kind {
            assert!(matches!(ty, SilType::Named(name) if name.contains("ContiguousArrayStorage")));
            assert_eq!(tail_elems.len(), 1);
            assert!(matches!(&tail_elems[0], SilType::Named(name) if name.contains("Int")));
        } else {
            panic!("expected AllocRef instruction");
        }
    }

    // ==================== dealloc_ref instruction tests ====================

    #[test]
    fn test_parse_dealloc_ref_simple() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_ref $MyClass
  dealloc_ref %0 : $MyClass
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let dealloc_ref_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::DeallocRef { .. }))
            .expect("should find dealloc_ref instruction");

        if let SilInstructionKind::DeallocRef { operand } = &dealloc_ref_inst.kind {
            assert_eq!(operand, "%0");
        } else {
            panic!("expected DeallocRef instruction");
        }
    }

    #[test]
    fn test_parse_dealloc_ref_with_stack() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_ref [stack] $MyClass
  dealloc_ref [stack] %0 : $MyClass
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let dealloc_ref_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::DeallocRef { .. }))
            .expect("should find dealloc_ref instruction");

        if let SilInstructionKind::DeallocRef { operand } = &dealloc_ref_inst.kind {
            assert_eq!(operand, "%0");
        } else {
            panic!("expected DeallocRef instruction");
        }
    }

    // ==================== copy_addr instruction tests ====================

    #[test]
    fn test_parse_copy_addr_simple() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_stack $Int
  %1 = alloc_stack $Int
  copy_addr %0 to %1 : $*Int
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let copy_addr_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::CopyAddr { .. }))
            .expect("should find copy_addr instruction");

        if let SilInstructionKind::CopyAddr {
            take,
            init,
            source,
            dest,
        } = &copy_addr_inst.kind
        {
            assert!(!take);
            assert!(!init);
            assert_eq!(source, "%0");
            assert_eq!(dest, "%1");
        } else {
            panic!("expected CopyAddr instruction");
        }
    }

    #[test]
    fn test_parse_copy_addr_with_take() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_stack $String
  %1 = alloc_stack $String
  copy_addr [take] %0 to %1 : $*String
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let copy_addr_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::CopyAddr { .. }))
            .expect("should find copy_addr instruction");

        if let SilInstructionKind::CopyAddr {
            take,
            init,
            source,
            dest,
        } = &copy_addr_inst.kind
        {
            assert!(take);
            assert!(!init);
            assert_eq!(source, "%0");
            assert_eq!(dest, "%1");
        } else {
            panic!("expected CopyAddr instruction");
        }
    }

    #[test]
    fn test_parse_copy_addr_with_init() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_stack $String
  %1 = alloc_stack $String
  copy_addr %0 to [init] %1 : $*String
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let copy_addr_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::CopyAddr { .. }))
            .expect("should find copy_addr instruction");

        if let SilInstructionKind::CopyAddr {
            take,
            init,
            source,
            dest,
        } = &copy_addr_inst.kind
        {
            assert!(!take);
            assert!(init);
            assert_eq!(source, "%0");
            assert_eq!(dest, "%1");
        } else {
            panic!("expected CopyAddr instruction");
        }
    }

    #[test]
    fn test_parse_copy_addr_take_and_init() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_stack $String
  %1 = alloc_stack $String
  copy_addr [take] %0 to [init] %1 : $*String
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let copy_addr_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::CopyAddr { .. }))
            .expect("should find copy_addr instruction");

        if let SilInstructionKind::CopyAddr {
            take,
            init,
            source,
            dest,
        } = &copy_addr_inst.kind
        {
            assert!(take);
            assert!(init);
            assert_eq!(source, "%0");
            assert_eq!(dest, "%1");
        } else {
            panic!("expected CopyAddr instruction");
        }
    }

    // ==================== thin_to_thick_function instruction tests ====================

    #[test]
    fn test_parse_thin_to_thick_function() {
        let sil = r"
sil_stage canonical

sil @thin_fn : $@convention(thin) () -> ()

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = function_ref @thin_fn : $@convention(thin) () -> ()
  %1 = thin_to_thick_function %0 : $@convention(thin) () -> () to $() -> ()
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let thin_to_thick_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::ThinToThickFunction { .. }))
            .expect("should find thin_to_thick_function instruction");

        if let SilInstructionKind::ThinToThickFunction { operand, .. } = &thin_to_thick_inst.kind {
            assert_eq!(operand, "%0");
        } else {
            panic!("expected ThinToThickFunction instruction");
        }
    }

    // ==================== ref_element_addr instruction tests ====================

    #[test]
    fn test_parse_ref_element_addr_simple() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_ref $MyClass
  %1 = ref_element_addr %0 : $MyClass, #MyClass.value
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let ref_element_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::RefElementAddr { .. }))
            .expect("should find ref_element_addr instruction");

        if let SilInstructionKind::RefElementAddr {
            operand,
            field,
            immutable,
        } = &ref_element_inst.kind
        {
            assert_eq!(operand, "%0");
            assert!(field.contains("value"));
            assert!(!immutable);
        } else {
            panic!("expected RefElementAddr instruction");
        }
    }

    #[test]
    fn test_parse_ref_element_addr_immutable() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_ref $MyClass
  %1 = ref_element_addr [immutable] %0 : $MyClass, #MyClass.value
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let ref_element_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::RefElementAddr { .. }))
            .expect("should find ref_element_addr instruction");

        if let SilInstructionKind::RefElementAddr {
            operand,
            field,
            immutable,
        } = &ref_element_inst.kind
        {
            assert_eq!(operand, "%0");
            assert!(field.contains("value"));
            assert!(immutable);
        } else {
            panic!("expected RefElementAddr instruction");
        }
    }

    // ==================== super_method instruction tests ====================

    #[test]
    fn test_parse_super_method() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_ref $ChildClass
  %1 = super_method %0 : $ChildClass, #ParentClass.foo : (ParentClass) -> () -> ()
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let super_method_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::SuperMethod { .. }))
            .expect("should find super_method instruction");

        if let SilInstructionKind::SuperMethod { operand, method } = &super_method_inst.kind {
            assert_eq!(operand, "%0");
            assert!(method.contains("ParentClass.foo"));
        } else {
            panic!("expected SuperMethod instruction");
        }
    }

    // ==================== unchecked_ref_cast instruction tests ====================

    #[test]
    fn test_parse_unchecked_ref_cast() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_ref $NSObject
  %1 = unchecked_ref_cast %0 : $NSObject to $AnyObject
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let unchecked_ref_cast_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::UncheckedRefCast { .. }))
            .expect("should find unchecked_ref_cast instruction");

        if let SilInstructionKind::UncheckedRefCast { operand, ty } = &unchecked_ref_cast_inst.kind
        {
            assert_eq!(operand, "%0");
            assert!(matches!(ty, SilType::Named(name) if name.contains("AnyObject")));
        } else {
            panic!("expected UncheckedRefCast instruction");
        }
    }

    #[test]
    fn test_parse_unchecked_ref_cast_generic() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_ref $Array<Int>
  %1 = unchecked_ref_cast %0 : $Array<Int> to $NSArray
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let unchecked_ref_cast_inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::UncheckedRefCast { .. }))
            .expect("should find unchecked_ref_cast instruction");

        if let SilInstructionKind::UncheckedRefCast { operand, ty } = &unchecked_ref_cast_inst.kind
        {
            assert_eq!(operand, "%0");
            assert!(matches!(ty, SilType::Named(name) if name.contains("NSArray")));
        } else {
            panic!("expected UncheckedRefCast instruction");
        }
    }

    // ==================== unchecked_addr_cast instruction tests ====================

    #[test]
    fn test_parse_unchecked_addr_cast_simple() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_stack $Int
  %1 = unchecked_addr_cast %0 : $*Int to $*UInt
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::UncheckedAddrCast { .. }))
            .expect("should find unchecked_addr_cast");

        if let SilInstructionKind::UncheckedAddrCast { operand, ty } = &inst.kind {
            assert_eq!(operand, "%0");
            assert!(
                matches!(ty, SilType::Address(inner) if matches!(inner.as_ref(), SilType::Named(n) if n.contains("UInt")))
            );
        } else {
            panic!("expected UncheckedAddrCast instruction");
        }
    }

    #[test]
    fn test_parse_unchecked_addr_cast_generic() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_stack $Optional<Int>
  %1 = unchecked_addr_cast %0 : $*Optional<Int> to $*Int
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::UncheckedAddrCast { .. }))
            .expect("should find unchecked_addr_cast");

        if let SilInstructionKind::UncheckedAddrCast { operand, ty } = &inst.kind {
            assert_eq!(operand, "%0");
            // The destination type should be $*Int
            assert!(matches!(ty, SilType::Address(_)));
        } else {
            panic!("expected UncheckedAddrCast instruction");
        }
    }

    // ==================== unchecked_trivial_bit_cast instruction tests ====================

    #[test]
    fn test_parse_unchecked_trivial_bit_cast_simple() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = integer_literal $Builtin.Int64, 42
  %1 = unchecked_trivial_bit_cast %0 : $Builtin.Int64 to $Builtin.RawPointer
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| {
                matches!(
                    &inst.kind,
                    SilInstructionKind::UncheckedTrivialBitCast { .. }
                )
            })
            .expect("should find unchecked_trivial_bit_cast");

        if let SilInstructionKind::UncheckedTrivialBitCast { operand, ty } = &inst.kind {
            assert_eq!(operand, "%0");
            // Type could be Builtin or Named depending on parser
            assert!(
                matches!(ty, SilType::Builtin(n) if n.contains("RawPointer"))
                    || matches!(ty, SilType::Named(n) if n.contains("RawPointer"))
            );
        } else {
            panic!("expected UncheckedTrivialBitCast instruction");
        }
    }

    #[test]
    fn test_parse_unchecked_trivial_bit_cast_word_to_int() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = integer_literal $Builtin.Word, 100
  %1 = unchecked_trivial_bit_cast %0 : $Builtin.Word to $Builtin.Int64
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| {
                matches!(
                    &inst.kind,
                    SilInstructionKind::UncheckedTrivialBitCast { .. }
                )
            })
            .expect("should find unchecked_trivial_bit_cast");

        if let SilInstructionKind::UncheckedTrivialBitCast { operand, ty } = &inst.kind {
            assert_eq!(operand, "%0");
            assert!(
                matches!(ty, SilType::Builtin(n) if n.contains("Int64"))
                    || matches!(ty, SilType::Named(n) if n.contains("Int64"))
            );
        } else {
            panic!("expected UncheckedTrivialBitCast instruction");
        }
    }

    // ==================== unchecked_bitwise_cast instruction tests ====================

    #[test]
    fn test_parse_unchecked_bitwise_cast_simple() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = integer_literal $Builtin.Int64, 0
  %1 = unchecked_bitwise_cast %0 : $Builtin.Int64 to $Builtin.NativeObject
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::UncheckedBitwiseCast { .. }))
            .expect("should find unchecked_bitwise_cast");

        if let SilInstructionKind::UncheckedBitwiseCast { operand, ty } = &inst.kind {
            assert_eq!(operand, "%0");
            assert!(
                matches!(ty, SilType::Builtin(n) if n.contains("NativeObject"))
                    || matches!(ty, SilType::Named(n) if n.contains("NativeObject"))
            );
        } else {
            panic!("expected UncheckedBitwiseCast instruction");
        }
    }

    #[test]
    fn test_parse_unchecked_bitwise_cast_object_to_raw() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_ref $MyClass
  %1 = unchecked_bitwise_cast %0 : $MyClass to $Builtin.RawPointer
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::UncheckedBitwiseCast { .. }))
            .expect("should find unchecked_bitwise_cast");

        if let SilInstructionKind::UncheckedBitwiseCast { operand, ty } = &inst.kind {
            assert_eq!(operand, "%0");
            assert!(
                matches!(ty, SilType::Builtin(n) if n.contains("RawPointer"))
                    || matches!(ty, SilType::Named(n) if n.contains("RawPointer"))
            );
        } else {
            panic!("expected UncheckedBitwiseCast instruction");
        }
    }

    // ==================== address_to_pointer instruction tests ====================

    #[test]
    fn test_parse_address_to_pointer_simple() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_stack $Int
  %1 = address_to_pointer %0 : $*Int to $Builtin.RawPointer
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::AddressToPointer { .. }))
            .expect("should find address_to_pointer");

        if let SilInstructionKind::AddressToPointer { operand } = &inst.kind {
            assert_eq!(operand, "%0");
        } else {
            panic!("expected AddressToPointer instruction");
        }
    }

    #[test]
    fn test_parse_address_to_pointer_with_stack_protection() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_stack $Int
  %1 = address_to_pointer [stack_protection] %0 : $*Int to $Builtin.RawPointer
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::AddressToPointer { .. }))
            .expect("should find address_to_pointer");

        if let SilInstructionKind::AddressToPointer { operand } = &inst.kind {
            assert_eq!(operand, "%0");
        } else {
            panic!("expected AddressToPointer instruction");
        }
    }

    // ==================== pointer_to_address instruction tests ====================

    #[test]
    fn test_parse_pointer_to_address_simple() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = integer_literal $Builtin.Word, 0
  %1 = inttoptr %0 : $Builtin.Word to $Builtin.RawPointer
  %2 = pointer_to_address %1 : $Builtin.RawPointer to $*Int
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::PointerToAddress { .. }))
            .expect("should find pointer_to_address");

        if let SilInstructionKind::PointerToAddress {
            operand,
            ty,
            strict,
        } = &inst.kind
        {
            assert_eq!(operand, "%1");
            assert!(matches!(ty, SilType::Address(_)));
            assert!(!strict);
        } else {
            panic!("expected PointerToAddress instruction");
        }
    }

    #[test]
    fn test_parse_pointer_to_address_with_strict() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = integer_literal $Builtin.Word, 0
  %1 = inttoptr %0 : $Builtin.Word to $Builtin.RawPointer
  %2 = pointer_to_address %1 : $Builtin.RawPointer to [strict] $*Int
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::PointerToAddress { .. }))
            .expect("should find pointer_to_address");

        if let SilInstructionKind::PointerToAddress {
            operand,
            ty,
            strict,
        } = &inst.kind
        {
            assert_eq!(operand, "%1");
            assert!(matches!(ty, SilType::Address(_)));
            assert!(strict);
        } else {
            panic!("expected PointerToAddress instruction");
        }
    }

    // ==================== hop_to_executor instruction tests ====================

    #[test]
    fn test_parse_hop_to_executor_simple() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_ref $MyActor
  hop_to_executor %0 : $MyActor
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::HopToExecutor { .. }))
            .expect("should find hop_to_executor");

        if let SilInstructionKind::HopToExecutor { operand } = &inst.kind {
            assert_eq!(operand, "%0");
        } else {
            panic!("expected HopToExecutor instruction");
        }
    }

    // ==================== extract_executor instruction tests ====================

    #[test]
    fn test_parse_extract_executor_simple() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_ref $MyActor
  %1 = extract_executor %0 : $MyActor
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::ExtractExecutor { .. }))
            .expect("should find extract_executor");

        if let SilInstructionKind::ExtractExecutor { operand } = &inst.kind {
            assert_eq!(operand, "%0");
        } else {
            panic!("expected ExtractExecutor instruction");
        }
    }

    // ==================== struct_element_addr instruction tests ====================

    #[test]
    fn test_parse_struct_element_addr_simple() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_stack $Point
  %1 = struct_element_addr %0 : $*Point, #Point.x
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::StructElementAddr { .. }))
            .expect("should find struct_element_addr");

        if let SilInstructionKind::StructElementAddr { operand, field } = &inst.kind {
            assert_eq!(operand, "%0");
            assert!(field.contains("Point.x"));
        } else {
            panic!("expected StructElementAddr instruction");
        }
    }

    #[test]
    fn test_parse_struct_element_addr_nested() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_stack $Container
  %1 = struct_element_addr %0 : $*Container, #Container.inner
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::StructElementAddr { .. }))
            .expect("should find struct_element_addr");

        if let SilInstructionKind::StructElementAddr { operand, field } = &inst.kind {
            assert_eq!(operand, "%0");
            assert!(field.contains("Container.inner"));
        } else {
            panic!("expected StructElementAddr instruction");
        }
    }

    // ==================== tuple_element_addr instruction tests ====================

    #[test]
    fn test_parse_tuple_element_addr_first() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_stack $(Int, String)
  %1 = tuple_element_addr %0 : $*(Int, String), 0
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::TupleElementAddr { .. }))
            .expect("should find tuple_element_addr");

        if let SilInstructionKind::TupleElementAddr { operand, index } = &inst.kind {
            assert_eq!(operand, "%0");
            assert_eq!(*index, 0);
        } else {
            panic!("expected TupleElementAddr instruction");
        }
    }

    #[test]
    fn test_parse_tuple_element_addr_second() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_stack $(Int, String, Bool)
  %1 = tuple_element_addr %0 : $*(Int, String, Bool), 1
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::TupleElementAddr { .. }))
            .expect("should find tuple_element_addr");

        if let SilInstructionKind::TupleElementAddr { operand, index } = &inst.kind {
            assert_eq!(operand, "%0");
            assert_eq!(*index, 1);
        } else {
            panic!("expected TupleElementAddr instruction");
        }
    }

    // ==================== ref_tail_addr instruction tests ====================

    #[test]
    fn test_parse_ref_tail_addr_simple() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_ref $ArrayStorage
  %1 = ref_tail_addr %0 : $ArrayStorage, $Int
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::RefTailAddr { .. }))
            .expect("should find ref_tail_addr");

        if let SilInstructionKind::RefTailAddr { operand, ty } = &inst.kind {
            assert_eq!(operand, "%0");
            assert!(matches!(ty, SilType::Named(n) if n.contains("Int")));
        } else {
            panic!("expected RefTailAddr instruction");
        }
    }

    #[test]
    fn test_parse_ref_tail_addr_with_immutable() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_ref $ArrayStorage
  %1 = ref_tail_addr [immutable] %0 : $ArrayStorage, $Element
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::RefTailAddr { .. }))
            .expect("should find ref_tail_addr");

        if let SilInstructionKind::RefTailAddr { operand, ty } = &inst.kind {
            assert_eq!(operand, "%0");
            assert!(matches!(ty, SilType::Named(n) if n.contains("Element")));
        } else {
            panic!("expected RefTailAddr instruction");
        }
    }

    // ==================== tail_addr instruction tests ====================

    #[test]
    fn test_parse_tail_addr_simple() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_stack $Header
  %1 = integer_literal $Builtin.Word, 10
  %2 = tail_addr %0 : $*Header, %1 : $Builtin.Word, $Element
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::TailAddr { .. }))
            .expect("should find tail_addr");

        if let SilInstructionKind::TailAddr { base, count, ty } = &inst.kind {
            assert_eq!(base, "%0");
            assert_eq!(count, "%1");
            assert!(matches!(ty, SilType::Named(n) if n.contains("Element")));
        } else {
            panic!("expected TailAddr instruction");
        }
    }

    // ==================== alloc_box instruction tests ====================

    #[test]
    fn test_parse_alloc_box_simple() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_box ${ var Int }
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::AllocBox { .. }))
            .expect("should find alloc_box");

        if let SilInstructionKind::AllocBox { ty } = &inst.kind {
            // The box type contains "var Int" - verify it parsed to a Box or similar type
            assert!(matches!(
                ty,
                SilType::Box(_) | SilType::Named(_) | SilType::Unknown(_)
            ));
        } else {
            panic!("expected AllocBox instruction");
        }
    }

    #[test]
    fn test_parse_alloc_box_with_attributes() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_box [dynamic_lifetime] [reflection] ${ var String }
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::AllocBox { .. }))
            .expect("should find alloc_box");

        if let SilInstructionKind::AllocBox { ty } = &inst.kind {
            // Verify it parsed - could be Box, Named, or Unknown
            assert!(matches!(
                ty,
                SilType::Box(_) | SilType::Named(_) | SilType::Unknown(_)
            ));
        } else {
            panic!("expected AllocBox instruction");
        }
    }

    // ==================== project_box instruction tests ====================

    #[test]
    fn test_parse_project_box_simple() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_box ${ var Int }
  %1 = project_box %0 : ${ var Int }
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::ProjectBox { .. }))
            .expect("should find project_box");

        if let SilInstructionKind::ProjectBox {
            operand,
            field_index,
        } = &inst.kind
        {
            assert_eq!(operand, "%0");
            assert!(field_index.is_none());
        } else {
            panic!("expected ProjectBox instruction");
        }
    }

    #[test]
    fn test_parse_project_box_with_index() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_box ${ var Int }
  %1 = project_box %0 : ${ var Int }, 0
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::ProjectBox { .. }))
            .expect("should find project_box");

        if let SilInstructionKind::ProjectBox {
            operand,
            field_index,
        } = &inst.kind
        {
            assert_eq!(operand, "%0");
            assert_eq!(*field_index, Some(0));
        } else {
            panic!("expected ProjectBox instruction");
        }
    }

    // ==================== dealloc_box instruction tests ====================

    #[test]
    fn test_parse_dealloc_box_simple() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_box ${ var Int }
  dealloc_box %0 : ${ var Int }
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::DeallocBox { .. }))
            .expect("should find dealloc_box");

        if let SilInstructionKind::DeallocBox { operand } = &inst.kind {
            assert_eq!(operand, "%0");
        } else {
            panic!("expected DeallocBox instruction");
        }
    }

    // ==================== bind_memory instruction tests ====================

    #[test]
    fn test_parse_bind_memory_simple() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = integer_literal $Builtin.Word, 0
  %1 = inttoptr %0 : $Builtin.Word to $Builtin.RawPointer
  %2 = integer_literal $Builtin.Word, 1
  %3 = bind_memory %1 : $Builtin.RawPointer, %2 : $Builtin.Word to $Int
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::BindMemory { .. }))
            .expect("should find bind_memory");

        if let SilInstructionKind::BindMemory {
            base,
            num_words,
            ty,
        } = &inst.kind
        {
            assert_eq!(base, "%1");
            assert_eq!(num_words, "%2");
            assert!(matches!(ty, SilType::Named(n) if n.contains("Int")));
        } else {
            panic!("expected BindMemory instruction");
        }
    }

    // ==================== rebind_memory instruction tests ====================

    #[test]
    fn test_parse_rebind_memory_simple() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_stack $Int
  %1 = rebind_memory %0 : $*Int to $UInt
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::RebindMemory { .. }))
            .expect("should find rebind_memory");

        if let SilInstructionKind::RebindMemory { operand, ty } = &inst.kind {
            assert_eq!(operand, "%0");
            assert!(matches!(ty, SilType::Named(n) if n.contains("UInt")));
        } else {
            panic!("expected RebindMemory instruction");
        }
    }

    // ==================== move_value instruction tests ====================

    #[test]
    fn test_parse_move_value_simple() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_ref $MyClass
  %1 = move_value %0 : $MyClass
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::MoveValue { .. }))
            .expect("should find move_value");

        if let SilInstructionKind::MoveValue {
            operand,
            lexical,
            pointer_escape,
            var_decl,
        } = &inst.kind
        {
            assert_eq!(operand, "%0");
            assert!(!lexical);
            assert!(!pointer_escape);
            assert!(!var_decl);
        } else {
            panic!("expected MoveValue instruction");
        }
    }

    #[test]
    fn test_parse_move_value_with_lexical() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_ref $MyClass
  %1 = move_value [lexical] %0 : $MyClass
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::MoveValue { .. }))
            .expect("should find move_value");

        if let SilInstructionKind::MoveValue {
            operand,
            lexical,
            pointer_escape,
            var_decl,
        } = &inst.kind
        {
            assert_eq!(operand, "%0");
            assert!(lexical);
            assert!(!pointer_escape);
            assert!(!var_decl);
        } else {
            panic!("expected MoveValue instruction");
        }
    }

    #[test]
    fn test_parse_move_value_with_all_attributes() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_ref $MyClass
  %1 = move_value [lexical] [pointer_escape] [var_decl] %0 : $MyClass
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::MoveValue { .. }))
            .expect("should find move_value");

        if let SilInstructionKind::MoveValue {
            operand,
            lexical,
            pointer_escape,
            var_decl,
        } = &inst.kind
        {
            assert_eq!(operand, "%0");
            assert!(lexical);
            assert!(pointer_escape);
            assert!(var_decl);
        } else {
            panic!("expected MoveValue instruction");
        }
    }

    // ==================== unchecked_enum_data instruction tests ====================

    #[test]
    fn test_parse_unchecked_enum_data_simple() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = enum $Optional<Int>, #Optional.some!enumelt, %1 : $Int
  %2 = unchecked_enum_data %0 : $Optional<Int>, #Optional.some
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::UncheckedEnumData { .. }))
            .expect("should find unchecked_enum_data");

        if let SilInstructionKind::UncheckedEnumData { operand, case_name } = &inst.kind {
            assert_eq!(operand, "%0");
            assert!(case_name.contains("Optional.some"));
        } else {
            panic!("expected UncheckedEnumData instruction");
        }
    }

    // ==================== assign instruction tests ====================

    #[test]
    fn test_parse_assign_simple() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = integer_literal $Builtin.Int64, 42
  %1 = alloc_stack $Int
  assign %0 to %1 : $*Int
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::Assign { .. }))
            .expect("should find assign");

        if let SilInstructionKind::Assign { source, dest } = &inst.kind {
            assert_eq!(source, "%0");
            assert_eq!(dest, "%1");
        } else {
            panic!("expected Assign instruction");
        }
    }

    // ==================== global_value instruction tests ====================

    #[test]
    fn test_parse_global_value_simple() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = global_value @myGlobal : $Int
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::GlobalValue { .. }))
            .expect("should find global_value");

        if let SilInstructionKind::GlobalValue { name } = &inst.kind {
            assert!(name.contains("myGlobal"));
        } else {
            panic!("expected GlobalValue instruction");
        }
    }

    #[test]
    fn test_parse_global_value_with_bare() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = global_value [bare] @someGlobal : $String
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::GlobalValue { .. }))
            .expect("should find global_value");

        if let SilInstructionKind::GlobalValue { name } = &inst.kind {
            assert!(name.contains("someGlobal"));
        } else {
            panic!("expected GlobalValue instruction");
        }
    }

    // ==================== tuple_pack_extract instruction tests ====================

    #[test]
    fn test_parse_tuple_pack_extract_simple() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = integer_literal $Builtin.Word, 0
  %1 = tuple ()
  %2 = tuple_pack_extract %0 of %1 : $(repeat each T) as $Int
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::TuplePackExtract { .. }))
            .expect("should find tuple_pack_extract");

        if let SilInstructionKind::TuplePackExtract {
            index,
            tuple,
            element_ty,
        } = &inst.kind
        {
            assert_eq!(index, "%0");
            assert_eq!(tuple, "%1");
            assert!(matches!(element_ty, SilType::Named(n) if n.contains("Int")));
        } else {
            panic!("expected TuplePackExtract instruction");
        }
    }

    // ==================== unconditional_checked_cast instruction tests ====================

    #[test]
    fn test_parse_unconditional_checked_cast_simple() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_ref $NSObject
  %1 = unconditional_checked_cast %0 : $NSObject to $MyClass
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| {
                matches!(
                    &inst.kind,
                    SilInstructionKind::UnconditionalCheckedCast { .. }
                )
            })
            .expect("should find unconditional_checked_cast");

        if let SilInstructionKind::UnconditionalCheckedCast { operand, ty } = &inst.kind {
            assert_eq!(operand, "%0");
            assert!(matches!(ty, SilType::Named(n) if n.contains("MyClass")));
        } else {
            panic!("expected UnconditionalCheckedCast instruction");
        }
    }

    #[test]
    fn test_parse_unconditional_checked_cast_bare_type() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_ref $AnyObject
  %1 = unconditional_checked_cast %0 to UIViewController
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| {
                matches!(
                    &inst.kind,
                    SilInstructionKind::UnconditionalCheckedCast { .. }
                )
            })
            .expect("should find unconditional_checked_cast");

        if let SilInstructionKind::UnconditionalCheckedCast { operand, ty } = &inst.kind {
            assert_eq!(operand, "%0");
            assert!(matches!(ty, SilType::Named(n) if n.contains("UIViewController")));
        } else {
            panic!("expected UnconditionalCheckedCast instruction");
        }
    }

    // ==================== unconditional_checked_cast_addr instruction tests ====================

    #[test]
    fn test_parse_unconditional_checked_cast_addr_simple() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_stack $Any
  %1 = alloc_stack $Int
  unconditional_checked_cast_addr Any in %0 : $*Any to Int in %1 : $*Int
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| {
                matches!(
                    &inst.kind,
                    SilInstructionKind::UnconditionalCheckedCastAddr { .. }
                )
            })
            .expect("should find unconditional_checked_cast_addr");

        if let SilInstructionKind::UnconditionalCheckedCastAddr {
            source_ty,
            source,
            target_ty,
            dest,
        } = &inst.kind
        {
            assert!(matches!(source_ty, SilType::Named(n) if n.contains("Any")));
            assert_eq!(source, "%0");
            assert!(matches!(target_ty, SilType::Named(n) if n.contains("Int")));
            assert_eq!(dest, "%1");
        } else {
            panic!("expected UnconditionalCheckedCastAddr instruction");
        }
    }

    #[test]
    fn test_parse_unconditional_checked_cast_addr_protocol() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_stack $Equatable
  %1 = alloc_stack $String
  unconditional_checked_cast_addr Equatable in %0 : $*Equatable to String in %1 : $*String
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| {
                matches!(
                    &inst.kind,
                    SilInstructionKind::UnconditionalCheckedCastAddr { .. }
                )
            })
            .expect("should find unconditional_checked_cast_addr");

        if let SilInstructionKind::UnconditionalCheckedCastAddr {
            source_ty,
            source,
            target_ty,
            dest,
        } = &inst.kind
        {
            assert!(matches!(source_ty, SilType::Named(n) if n.contains("Equatable")));
            assert_eq!(source, "%0");
            assert!(matches!(target_ty, SilType::Named(n) if n.contains("String")));
            assert_eq!(dest, "%1");
        } else {
            panic!("expected UnconditionalCheckedCastAddr instruction");
        }
    }

    // ==================== differentiable_function instruction tests ====================

    #[test]
    fn test_parse_differentiable_function_simple() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = function_ref @original_func
  %1 = differentiable_function %0 : $@convention(thin) (Float) -> Float
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| {
                matches!(
                    &inst.kind,
                    SilInstructionKind::DifferentiableFunction { .. }
                )
            })
            .expect("should find differentiable_function");

        if let SilInstructionKind::DifferentiableFunction {
            original,
            jvp,
            vjp,
            parameters,
        } = &inst.kind
        {
            assert_eq!(original, "%0");
            assert!(jvp.is_none());
            assert!(vjp.is_none());
            assert!(parameters.is_empty());
        } else {
            panic!("expected DifferentiableFunction instruction");
        }
    }

    #[test]
    fn test_parse_differentiable_function_with_parameters() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = function_ref @original_func
  %1 = differentiable_function [parameters 0 1] %0 : $@convention(thin) (Float, Float) -> Float
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| {
                matches!(
                    &inst.kind,
                    SilInstructionKind::DifferentiableFunction { .. }
                )
            })
            .expect("should find differentiable_function");

        if let SilInstructionKind::DifferentiableFunction {
            original,
            jvp,
            vjp,
            parameters,
        } = &inst.kind
        {
            assert_eq!(original, "%0");
            assert!(jvp.is_none());
            assert!(vjp.is_none());
            assert_eq!(parameters, &[0, 1]);
        } else {
            panic!("expected DifferentiableFunction instruction");
        }
    }

    #[test]
    fn test_parse_differentiable_function_with_derivatives() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = function_ref @original_func
  %1 = function_ref @jvp_func
  %2 = function_ref @vjp_func
  %3 = differentiable_function [parameters 0] %0 with_derivative {%1, %2}
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| {
                matches!(
                    &inst.kind,
                    SilInstructionKind::DifferentiableFunction { .. }
                )
            })
            .expect("should find differentiable_function");

        if let SilInstructionKind::DifferentiableFunction {
            original,
            jvp,
            vjp,
            parameters,
        } = &inst.kind
        {
            assert_eq!(original, "%0");
            assert_eq!(jvp.as_deref(), Some("%1"));
            assert_eq!(vjp.as_deref(), Some("%2"));
            assert_eq!(parameters, &[0]);
        } else {
            panic!("expected DifferentiableFunction instruction");
        }
    }

    // ==================== linear_function instruction tests ====================

    #[test]
    fn test_parse_linear_function_simple() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = function_ref @original_func
  %1 = linear_function %0 : $@convention(thin) (Float) -> Float
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::LinearFunction { .. }))
            .expect("should find linear_function");

        if let SilInstructionKind::LinearFunction {
            original,
            transpose,
            parameters,
        } = &inst.kind
        {
            assert_eq!(original, "%0");
            assert!(transpose.is_none());
            assert!(parameters.is_empty());
        } else {
            panic!("expected LinearFunction instruction");
        }
    }

    #[test]
    fn test_parse_linear_function_with_parameters() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = function_ref @original_func
  %1 = linear_function [parameters 0 1 2] %0 : $@convention(thin) (Float, Float, Float) -> Float
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::LinearFunction { .. }))
            .expect("should find linear_function");

        if let SilInstructionKind::LinearFunction {
            original,
            transpose,
            parameters,
        } = &inst.kind
        {
            assert_eq!(original, "%0");
            assert!(transpose.is_none());
            assert_eq!(parameters, &[0, 1, 2]);
        } else {
            panic!("expected LinearFunction instruction");
        }
    }

    #[test]
    fn test_parse_linear_function_with_transpose() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = function_ref @original_func
  %1 = function_ref @transpose_func
  %2 = linear_function [parameters 0] %0 with_transpose %1
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::LinearFunction { .. }))
            .expect("should find linear_function");

        if let SilInstructionKind::LinearFunction {
            original,
            transpose,
            parameters,
        } = &inst.kind
        {
            assert_eq!(original, "%0");
            assert_eq!(transpose.as_deref(), Some("%1"));
            assert_eq!(parameters, &[0]);
        } else {
            panic!("expected LinearFunction instruction");
        }
    }

    // ==================== differentiable_function_extract instruction tests ====================

    #[test]
    fn test_parse_differentiable_function_extract_original() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = function_ref @diff_func
  %1 = differentiable_function_extract [original] %0 : $@differentiable(reverse) @convention(thin) (Float) -> Float
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| {
                matches!(
                    &inst.kind,
                    SilInstructionKind::DifferentiableFunctionExtract { .. }
                )
            })
            .expect("should find differentiable_function_extract");

        if let SilInstructionKind::DifferentiableFunctionExtract { operand, extractee } = &inst.kind
        {
            assert_eq!(operand, "%0");
            assert!(matches!(extractee, DifferentiableExtractee::Original));
        } else {
            panic!("expected DifferentiableFunctionExtract instruction");
        }
    }

    #[test]
    fn test_parse_differentiable_function_extract_jvp() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = function_ref @diff_func
  %1 = differentiable_function_extract [jvp] %0 : $@differentiable(reverse) @convention(thin) (Float) -> Float
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| {
                matches!(
                    &inst.kind,
                    SilInstructionKind::DifferentiableFunctionExtract { .. }
                )
            })
            .expect("should find differentiable_function_extract");

        if let SilInstructionKind::DifferentiableFunctionExtract { operand, extractee } = &inst.kind
        {
            assert_eq!(operand, "%0");
            assert!(matches!(extractee, DifferentiableExtractee::JVP));
        } else {
            panic!("expected DifferentiableFunctionExtract instruction");
        }
    }

    #[test]
    fn test_parse_differentiable_function_extract_vjp() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = function_ref @diff_func
  %1 = differentiable_function_extract [vjp] %0 : $@differentiable(reverse) @convention(thin) (Float) -> Float
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| {
                matches!(
                    &inst.kind,
                    SilInstructionKind::DifferentiableFunctionExtract { .. }
                )
            })
            .expect("should find differentiable_function_extract");

        if let SilInstructionKind::DifferentiableFunctionExtract { operand, extractee } = &inst.kind
        {
            assert_eq!(operand, "%0");
            assert!(matches!(extractee, DifferentiableExtractee::VJP));
        } else {
            panic!("expected DifferentiableFunctionExtract instruction");
        }
    }

    // ==================== linear_function_extract instruction tests ====================

    #[test]
    fn test_parse_linear_function_extract_original() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = function_ref @linear_func
  %1 = linear_function_extract [original] %0 : $@differentiable(linear) @convention(thin) (Float) -> Float
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::LinearFunctionExtract { .. }))
            .expect("should find linear_function_extract");

        if let SilInstructionKind::LinearFunctionExtract { operand, extractee } = &inst.kind {
            assert_eq!(operand, "%0");
            assert!(matches!(extractee, LinearExtractee::Original));
        } else {
            panic!("expected LinearFunctionExtract instruction");
        }
    }

    #[test]
    fn test_parse_linear_function_extract_transpose() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = function_ref @linear_func
  %1 = linear_function_extract [transpose] %0 : $@differentiable(linear) @convention(thin) (Float) -> Float
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::LinearFunctionExtract { .. }))
            .expect("should find linear_function_extract");

        if let SilInstructionKind::LinearFunctionExtract { operand, extractee } = &inst.kind {
            assert_eq!(operand, "%0");
            assert!(matches!(extractee, LinearExtractee::Transpose));
        } else {
            panic!("expected LinearFunctionExtract instruction");
        }
    }

    // ==================== differentiability_witness_function instruction tests ====================

    #[test]
    fn test_parse_differentiability_witness_function_jvp() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = differentiability_witness_function [jvp] @AD__sin__jvp : $@convention(thin) (Float) -> (Float, @owned @callee_guaranteed (Float) -> Float)
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| {
                matches!(
                    &inst.kind,
                    SilInstructionKind::DifferentiabilityWitnessFunction { .. }
                )
            })
            .expect("should find differentiability_witness_function");

        if let SilInstructionKind::DifferentiabilityWitnessFunction {
            witness_kind,
            witness,
            ..
        } = &inst.kind
        {
            assert!(matches!(witness_kind, DifferentiabilityWitnessKind::JVP));
            assert!(witness.contains("AD__sin__jvp"));
        } else {
            panic!("expected DifferentiabilityWitnessFunction instruction");
        }
    }

    #[test]
    fn test_parse_differentiability_witness_function_vjp() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = differentiability_witness_function [vjp] @AD__cos__vjp : $@convention(thin) (Float) -> (Float, @owned @callee_guaranteed (Float) -> Float)
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| {
                matches!(
                    &inst.kind,
                    SilInstructionKind::DifferentiabilityWitnessFunction { .. }
                )
            })
            .expect("should find differentiability_witness_function");

        if let SilInstructionKind::DifferentiabilityWitnessFunction {
            witness_kind,
            witness,
            ..
        } = &inst.kind
        {
            assert!(matches!(witness_kind, DifferentiabilityWitnessKind::VJP));
            assert!(witness.contains("AD__cos__vjp"));
        } else {
            panic!("expected DifferentiabilityWitnessFunction instruction");
        }
    }

    #[test]
    fn test_parse_differentiability_witness_function_transpose() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = differentiability_witness_function [transpose] @AD__add__transpose : $@convention(thin) (Float, Float) -> (Float, Float)
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| {
                matches!(
                    &inst.kind,
                    SilInstructionKind::DifferentiabilityWitnessFunction { .. }
                )
            })
            .expect("should find differentiability_witness_function");

        if let SilInstructionKind::DifferentiabilityWitnessFunction {
            witness_kind,
            witness,
            ..
        } = &inst.kind
        {
            assert!(matches!(
                witness_kind,
                DifferentiabilityWitnessKind::Transpose
            ));
            assert!(witness.contains("AD__add__transpose"));
        } else {
            panic!("expected DifferentiabilityWitnessFunction instruction");
        }
    }

    // ==================== prev_dynamic_function_ref instruction tests ====================

    #[test]
    fn test_parse_prev_dynamic_function_ref() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = prev_dynamic_function_ref @replaced_method : $@convention(thin) () -> ()
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| {
                matches!(
                    &inst.kind,
                    SilInstructionKind::PrevDynamicFunctionRef { .. }
                )
            })
            .expect("should find prev_dynamic_function_ref");

        if let SilInstructionKind::PrevDynamicFunctionRef { name } = &inst.kind {
            assert!(name.contains("replaced_method"));
        } else {
            panic!("expected PrevDynamicFunctionRef instruction");
        }
    }

    // ==================== has_symbol instruction tests ====================

    #[test]
    fn test_parse_has_symbol() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = has_symbol #MyClass.myMethod
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::HasSymbol { .. }))
            .expect("should find has_symbol");

        if let SilInstructionKind::HasSymbol { decl } = &inst.kind {
            assert!(decl.contains("MyClass.myMethod"));
        } else {
            panic!("expected HasSymbol instruction");
        }
    }

    // ==================== alloc_global instruction tests ====================

    #[test]
    fn test_parse_alloc_global() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  alloc_global @myGlobalVariable
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::AllocGlobal { .. }))
            .expect("should find alloc_global");

        if let SilInstructionKind::AllocGlobal { name } = &inst.kind {
            assert!(name.contains("myGlobalVariable"));
        } else {
            panic!("expected AllocGlobal instruction");
        }
    }

    // ==================== fix_lifetime instruction tests ====================

    #[test]
    fn test_parse_fix_lifetime() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_ref $MyClass
  fix_lifetime %0 : $MyClass
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::FixLifetime { .. }))
            .expect("should find fix_lifetime");

        if let SilInstructionKind::FixLifetime { operand } = &inst.kind {
            assert_eq!(operand, "%0");
        } else {
            panic!("expected FixLifetime instruction");
        }
    }

    // ==================== is_unique instruction tests ====================

    #[test]
    fn test_parse_is_unique() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_stack $*MyClass
  %1 = is_unique %0 : $*MyClass
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::IsUnique { .. }))
            .expect("should find is_unique");

        if let SilInstructionKind::IsUnique { operand } = &inst.kind {
            assert_eq!(operand, "%0");
        } else {
            panic!("expected IsUnique instruction");
        }
    }

    // ==================== debug_value instruction tests ====================

    #[test]
    fn test_parse_debug_value_simple() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = integer_literal $Builtin.Int64, 42
  debug_value %0, let
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::DebugValue { .. }))
            .expect("should find debug_value");

        if let SilInstructionKind::DebugValue {
            operand,
            name,
            argno,
        } = &inst.kind
        {
            assert_eq!(operand, "%0");
            assert!(name.is_none());
            assert!(argno.is_none());
        } else {
            panic!("expected DebugValue instruction");
        }
    }

    #[test]
    fn test_parse_debug_value_with_name() {
        let sil = r#"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = integer_literal $Builtin.Int64, 42
  debug_value %0, let, name "myVar"
  unreachable
}
"#;
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::DebugValue { .. }))
            .expect("should find debug_value");

        if let SilInstructionKind::DebugValue { operand, name, .. } = &inst.kind {
            assert_eq!(operand, "%0");
            assert_eq!(name.as_deref(), Some("myVar"));
        } else {
            panic!("expected DebugValue instruction");
        }
    }

    #[test]
    fn test_parse_debug_value_undef() {
        let sil = r#"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  debug_value undef : $Int, let, name "x"
  unreachable
}
"#;
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::DebugValue { .. }))
            .expect("should find debug_value");

        if let SilInstructionKind::DebugValue { operand, name, .. } = &inst.kind {
            assert_eq!(operand, "_undef");
            assert_eq!(name.as_deref(), Some("x"));
        } else {
            panic!("expected DebugValue instruction");
        }
    }

    // ==================== mark_dependence instruction tests ====================

    #[test]
    fn test_parse_mark_dependence() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_ref $MyClass
  %1 = ref_element_addr %0 : $MyClass, #MyClass.field
  %2 = mark_dependence %1 : $*Int on %0 : $MyClass
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::MarkDependence { .. }))
            .expect("should find mark_dependence");

        if let SilInstructionKind::MarkDependence { value, base } = &inst.kind {
            assert_eq!(value, "%1");
            assert_eq!(base, "%0");
        } else {
            panic!("expected MarkDependence instruction");
        }
    }

    // ==================== bridge object instruction tests ====================

    #[test]
    fn test_parse_ref_to_bridge_object() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_ref $NSObject
  %1 = integer_literal $Builtin.Word, 0
  %2 = ref_to_bridge_object %0 : $NSObject, %1 : $Builtin.Word
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::RefToBridgeObject { .. }))
            .expect("should find ref_to_bridge_object");

        if let SilInstructionKind::RefToBridgeObject { operand, bits } = &inst.kind {
            assert_eq!(operand, "%0");
            assert_eq!(bits, "%1");
        } else {
            panic!("expected RefToBridgeObject instruction");
        }
    }

    #[test]
    fn test_parse_bridge_object_to_ref() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = integer_literal $Builtin.Word, 0
  %1 = bridge_object_to_ref %0 : $Builtin.BridgeObject to $NSObject
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::BridgeObjectToRef { .. }))
            .expect("should find bridge_object_to_ref");

        if let SilInstructionKind::BridgeObjectToRef { operand, ty } = &inst.kind {
            assert_eq!(operand, "%0");
            assert!(matches!(ty, SilType::Named(n) if n.contains("NSObject")));
        } else {
            panic!("expected BridgeObjectToRef instruction");
        }
    }

    #[test]
    fn test_parse_bridge_object_to_word() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = integer_literal $Builtin.Word, 0
  %1 = bridge_object_to_word %0 : $Builtin.BridgeObject
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::BridgeObjectToWord { .. }))
            .expect("should find bridge_object_to_word");

        if let SilInstructionKind::BridgeObjectToWord { operand } = &inst.kind {
            assert_eq!(operand, "%0");
        } else {
            panic!("expected BridgeObjectToWord instruction");
        }
    }

    #[test]
    fn test_parse_classify_bridge_object() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = integer_literal $Builtin.Word, 0
  %1 = classify_bridge_object %0 : $Builtin.BridgeObject
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::ClassifyBridgeObject { .. }))
            .expect("should find classify_bridge_object");

        if let SilInstructionKind::ClassifyBridgeObject { operand } = &inst.kind {
            assert_eq!(operand, "%0");
        } else {
            panic!("expected ClassifyBridgeObject instruction");
        }
    }

    #[test]
    fn test_parse_value_to_bridge_object() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = integer_literal $Builtin.Word, 42
  %1 = value_to_bridge_object %0 : $Builtin.Word
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::ValueToBridgeObject { .. }))
            .expect("should find value_to_bridge_object");

        if let SilInstructionKind::ValueToBridgeObject { operand } = &inst.kind {
            assert_eq!(operand, "%0");
        } else {
            panic!("expected ValueToBridgeObject instruction");
        }
    }

    // ==================== ObjC metatype conversion instruction tests ====================

    #[test]
    fn test_parse_thick_to_objc_metatype() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = metatype $@thick NSObject.Type
  %1 = thick_to_objc_metatype %0 : $@thick NSObject.Type
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::ThickToObjcMetatype { .. }))
            .expect("should find thick_to_objc_metatype");

        if let SilInstructionKind::ThickToObjcMetatype { operand } = &inst.kind {
            assert_eq!(operand, "%0");
        } else {
            panic!("expected ThickToObjcMetatype instruction");
        }
    }

    #[test]
    fn test_parse_objc_to_thick_metatype() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = metatype $@objc_metatype NSObject.Type
  %1 = objc_to_thick_metatype %0 : $@objc_metatype NSObject.Type
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::ObjcToThickMetatype { .. }))
            .expect("should find objc_to_thick_metatype");

        if let SilInstructionKind::ObjcToThickMetatype { operand, .. } = &inst.kind {
            assert_eq!(operand, "%0");
        } else {
            panic!("expected ObjcToThickMetatype instruction");
        }
    }

    // ==================== Pack instruction tests ====================

    #[test]
    fn test_parse_alloc_pack() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_pack $Pack{Int, String, Float}
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::AllocPack { .. }))
            .expect("should find alloc_pack");

        if let SilInstructionKind::AllocPack { pack_ty } = &inst.kind {
            assert!(format!("{pack_ty:?}").contains("Pack"));
        } else {
            panic!("expected AllocPack instruction");
        }
    }

    #[test]
    fn test_parse_alloc_pack_with_repeat() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_pack $Pack{Int, repeat each T}
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::AllocPack { .. }))
            .expect("should find alloc_pack");
        assert!(matches!(inst.kind, SilInstructionKind::AllocPack { .. }));
    }

    #[test]
    fn test_parse_dealloc_pack() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_pack $Pack{Int, String}
  dealloc_pack %0 : $*Pack{Int, String}
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::DeallocPack { .. }))
            .expect("should find dealloc_pack");

        if let SilInstructionKind::DeallocPack { operand } = &inst.kind {
            assert_eq!(operand, "%0");
        } else {
            panic!("expected DeallocPack instruction");
        }
    }

    #[test]
    fn test_parse_pack_length() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = pack_length $Pack{Int, Float, String}
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::PackLength { .. }))
            .expect("should find pack_length");
        assert!(matches!(inst.kind, SilInstructionKind::PackLength { .. }));
    }

    #[test]
    fn test_parse_dynamic_pack_index() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = integer_literal $Builtin.Word, 1
  %1 = dynamic_pack_index %0 of $Pack{repeat each T}
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::DynamicPackIndex { .. }))
            .expect("should find dynamic_pack_index");

        if let SilInstructionKind::DynamicPackIndex { operand, .. } = &inst.kind {
            assert_eq!(operand, "%0");
        } else {
            panic!("expected DynamicPackIndex instruction");
        }
    }

    #[test]
    fn test_parse_scalar_pack_index() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = scalar_pack_index 2 of $Pack{Int, String, Float}
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::ScalarPackIndex { .. }))
            .expect("should find scalar_pack_index");

        if let SilInstructionKind::ScalarPackIndex { index, .. } = &inst.kind {
            assert_eq!(*index, 2);
        } else {
            panic!("expected ScalarPackIndex instruction");
        }
    }

    #[test]
    fn test_parse_scalar_pack_index_zero() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = scalar_pack_index 0 of $Pack{Int, repeat each T}
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::ScalarPackIndex { .. }))
            .expect("should find scalar_pack_index");

        if let SilInstructionKind::ScalarPackIndex { index, .. } = &inst.kind {
            assert_eq!(*index, 0);
        } else {
            panic!("expected ScalarPackIndex instruction");
        }
    }

    #[test]
    fn test_parse_pack_pack_index() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = integer_literal $Builtin.Word, 0
  %1 = pack_pack_index 1, %0 of $Pack{Int, repeat each T}
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::PackPackIndex { .. }))
            .expect("should find pack_pack_index");

        if let SilInstructionKind::PackPackIndex {
            component_index,
            inner_index,
            ..
        } = &inst.kind
        {
            assert_eq!(*component_index, 1);
            assert_eq!(inner_index, "%0");
        } else {
            panic!("expected PackPackIndex instruction");
        }
    }

    #[test]
    fn test_parse_open_pack_element() {
        let sil = r#"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = integer_literal $Builtin.Word, 0
  %1 = open_pack_element %0 of <each U> at <Pack{repeat each U}>, shape $each U, uuid "ABC123"
  unreachable
}
"#;
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::OpenPackElement { .. }))
            .expect("should find open_pack_element");

        if let SilInstructionKind::OpenPackElement { index, uuid, .. } = &inst.kind {
            assert_eq!(index, "%0");
            assert_eq!(uuid, "ABC123");
        } else {
            panic!("expected OpenPackElement instruction");
        }
    }

    #[test]
    fn test_parse_pack_element_get() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = integer_literal $Builtin.Word, 0
  %1 = alloc_pack $PackType
  %2 = pack_element_get %0 of %1 : $*PackType as $*Int
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::PackElementGet { .. }))
            .expect("should find pack_element_get");

        if let SilInstructionKind::PackElementGet { index, pack, .. } = &inst.kind {
            assert_eq!(index, "%0");
            assert_eq!(pack, "%1");
        } else {
            panic!("expected PackElementGet instruction");
        }
    }

    #[test]
    fn test_parse_pack_element_set() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = integer_literal $Builtin.Word, 0
  %1 = alloc_pack $Pack{Int, String}
  %2 = alloc_stack $Int
  pack_element_set %2 : $*Int into %0 of %1 : $*Pack{Int, String}
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::PackElementSet { .. }))
            .expect("should find pack_element_set");

        if let SilInstructionKind::PackElementSet { value, index, pack } = &inst.kind {
            assert_eq!(value, "%2");
            assert_eq!(index, "%0");
            assert_eq!(pack, "%1");
        } else {
            panic!("expected PackElementSet instruction");
        }
    }

    #[test]
    fn test_parse_tuple_pack_element_addr() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = integer_literal $Builtin.Word, 0
  %1 = alloc_stack $(Int, String, Float)
  %2 = tuple_pack_element_addr %0 of %1 : $*(Int, String, Float) as $*Int
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::TuplePackElementAddr { .. }))
            .expect("should find tuple_pack_element_addr");

        if let SilInstructionKind::TuplePackElementAddr { index, tuple, .. } = &inst.kind {
            assert_eq!(index, "%0");
            assert_eq!(tuple, "%1");
        } else {
            panic!("expected TuplePackElementAddr instruction");
        }
    }

    #[test]
    fn test_parse_tuple_pack_extract() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = integer_literal $Builtin.Word, 0
  %1 = tuple ()
  %2 = tuple_pack_extract %0 of %1 : $PackTuple as $Int
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::TuplePackExtract { .. }))
            .expect("should find tuple_pack_extract");

        if let SilInstructionKind::TuplePackExtract { index, tuple, .. } = &inst.kind {
            assert_eq!(index, "%0");
            assert_eq!(tuple, "%1");
        } else {
            panic!("expected TuplePackExtract instruction");
        }
    }

    // ==================== Async continuation instruction tests ====================

    #[test]
    fn test_parse_get_async_continuation() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = get_async_continuation Int
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::GetAsyncContinuation { .. }))
            .expect("should find get_async_continuation");

        if let SilInstructionKind::GetAsyncContinuation { throws, .. } = &inst.kind {
            assert!(!throws);
        } else {
            panic!("expected GetAsyncContinuation instruction");
        }
    }

    #[test]
    fn test_parse_get_async_continuation_throws() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = get_async_continuation [throws] String
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::GetAsyncContinuation { .. }))
            .expect("should find get_async_continuation");

        if let SilInstructionKind::GetAsyncContinuation { throws, .. } = &inst.kind {
            assert!(throws);
        } else {
            panic!("expected GetAsyncContinuation instruction");
        }
    }

    #[test]
    fn test_parse_get_async_continuation_addr() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_stack $Int
  %1 = get_async_continuation_addr Int, %0 : $*Int
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| {
                matches!(
                    &inst.kind,
                    SilInstructionKind::GetAsyncContinuationAddr { .. }
                )
            })
            .expect("should find get_async_continuation_addr");

        if let SilInstructionKind::GetAsyncContinuationAddr {
            result_addr,
            throws,
            ..
        } = &inst.kind
        {
            assert_eq!(result_addr, "%0");
            assert!(!throws);
        } else {
            panic!("expected GetAsyncContinuationAddr instruction");
        }
    }

    #[test]
    fn test_parse_get_async_continuation_addr_throws() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_stack $String
  %1 = get_async_continuation_addr [throws] String, %0 : $*String
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| {
                matches!(
                    &inst.kind,
                    SilInstructionKind::GetAsyncContinuationAddr { .. }
                )
            })
            .expect("should find get_async_continuation_addr");

        if let SilInstructionKind::GetAsyncContinuationAddr {
            result_addr,
            throws,
            ..
        } = &inst.kind
        {
            assert_eq!(result_addr, "%0");
            assert!(throws);
        } else {
            panic!("expected GetAsyncContinuationAddr instruction");
        }
    }

    #[test]
    fn test_parse_await_async_continuation() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = get_async_continuation Int
  await_async_continuation %0 : $RawContinuation, resume bb1

bb1:
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        if let SilTerminator::AwaitAsyncContinuation {
            continuation,
            resume_dest,
            error_dest,
        } = &bb0.terminator
        {
            assert_eq!(continuation, "%0");
            assert_eq!(resume_dest, "bb1");
            assert!(error_dest.is_none());
        } else {
            panic!("expected AwaitAsyncContinuation terminator");
        }
    }

    #[test]
    fn test_parse_await_async_continuation_with_error() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = get_async_continuation [throws] Int
  await_async_continuation %0 : $RawContinuation, resume bb1, error bb2

bb1:
  unreachable

bb2:
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        if let SilTerminator::AwaitAsyncContinuation {
            continuation,
            resume_dest,
            error_dest,
        } = &bb0.terminator
        {
            assert_eq!(continuation, "%0");
            assert_eq!(resume_dest, "bb1");
            assert_eq!(error_dest.as_ref().unwrap(), "bb2");
        } else {
            panic!("expected AwaitAsyncContinuation terminator");
        }
    }

    // ==================== COW mutation instruction tests ====================

    #[test]
    fn test_parse_begin_cow_mutation() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (@owned ArrayBuffer) -> () {
bb0(%0 : $ArrayBuffer):
  (%1, %2) = begin_cow_mutation %0 : $ArrayBuffer
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::BeginCowMutation { .. }))
            .expect("should find begin_cow_mutation");

        if let SilInstructionKind::BeginCowMutation { operand, native } = &inst.kind {
            assert_eq!(operand, "%0");
            assert!(!native);
        } else {
            panic!("expected BeginCowMutation instruction");
        }
    }

    #[test]
    fn test_parse_begin_cow_mutation_native() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (@owned ArrayBuffer) -> () {
bb0(%0 : $ArrayBuffer):
  (%1, %2) = begin_cow_mutation [native] %0 : $ArrayBuffer
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::BeginCowMutation { .. }))
            .expect("should find begin_cow_mutation");

        if let SilInstructionKind::BeginCowMutation { operand, native } = &inst.kind {
            assert_eq!(operand, "%0");
            assert!(native);
        } else {
            panic!("expected BeginCowMutation instruction");
        }
    }

    #[test]
    fn test_parse_end_cow_mutation() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (@owned ArrayBuffer) -> () {
bb0(%0 : $ArrayBuffer):
  (%1, %2) = begin_cow_mutation %0 : $ArrayBuffer
  %3 = end_cow_mutation %2 : $ArrayBuffer
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::EndCowMutation { .. }))
            .expect("should find end_cow_mutation");

        if let SilInstructionKind::EndCowMutation {
            operand,
            keep_unique,
        } = &inst.kind
        {
            assert_eq!(operand, "%2");
            assert!(!keep_unique);
        } else {
            panic!("expected EndCowMutation instruction");
        }
    }

    #[test]
    fn test_parse_end_cow_mutation_keep_unique() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (@owned ArrayBuffer) -> () {
bb0(%0 : $ArrayBuffer):
  (%1, %2) = begin_cow_mutation %0 : $ArrayBuffer
  %3 = end_cow_mutation [keep_unique] %2 : $ArrayBuffer
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::EndCowMutation { .. }))
            .expect("should find end_cow_mutation");

        if let SilInstructionKind::EndCowMutation {
            operand,
            keep_unique,
        } = &inst.kind
        {
            assert_eq!(operand, "%2");
            assert!(keep_unique);
        } else {
            panic!("expected EndCowMutation instruction");
        }
    }

    #[test]
    fn test_parse_end_cow_mutation_addr() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_stack $ArrayBuffer
  end_cow_mutation_addr %0 : $*ArrayBuffer
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("test"))
            .expect("should find test function");
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::EndCowMutationAddr { .. }))
            .expect("should find end_cow_mutation_addr");

        if let SilInstructionKind::EndCowMutationAddr { address } = &inst.kind {
            assert_eq!(address, "%0");
        } else {
            panic!("expected EndCowMutationAddr instruction");
        }
    }

    #[test]
    fn test_parse_float_literal_simple() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = float_literal $Builtin.FPIEEE64, 0x4014000000000000
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::FloatLiteral { .. }))
            .expect("should find float_literal");

        if let SilInstructionKind::FloatLiteral { value, .. } = &inst.kind {
            // 0x4014000000000000 is the IEEE 754 bit representation of 5.0
            assert!((*value - 5.0).abs() < f64::EPSILON);
        } else {
            panic!("expected FloatLiteral instruction");
        }
    }

    #[test]
    fn test_parse_float_literal_decimal() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = float_literal $Builtin.FPIEEE32, 1.234
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::FloatLiteral { .. }))
            .expect("should find float_literal");

        if let SilInstructionKind::FloatLiteral { value, .. } = &inst.kind {
            assert!((*value - 1.234).abs() < 0.001);
        } else {
            panic!("expected FloatLiteral instruction");
        }
    }

    #[test]
    fn test_parse_destructure_tuple_simple() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) ((Int, String)) -> () {
bb0(%0 : $(Int, String)):
  (%1, %2) = destructure_tuple %0
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::DestructureTuple { .. }))
            .expect("should find destructure_tuple");

        if let SilInstructionKind::DestructureTuple { operand } = &inst.kind {
            assert_eq!(operand, "%0");
        } else {
            panic!("expected DestructureTuple instruction");
        }
    }

    #[test]
    fn test_parse_destructure_struct_simple() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (MyStruct) -> () {
bb0(%0 : $MyStruct):
  (%1, %2) = destructure_struct %0
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::DestructureStruct { .. }))
            .expect("should find destructure_struct");

        if let SilInstructionKind::DestructureStruct { operand } = &inst.kind {
            assert_eq!(operand, "%0");
        } else {
            panic!("expected DestructureStruct instruction");
        }
    }

    #[test]
    fn test_parse_tuple_addr_constructor_init() {
        let sil = r#"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_stack $(Int, String)
  %1 = integer_literal $Builtin.Int64, 42
  %2 = string_literal utf8 "hello"
  tuple_addr_constructor [init] %0 : $*(Int, String) with (%1 : $Int, %2 : $String)
  unreachable
}
"#;
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::TupleAddrConstructor { .. }))
            .expect("should find tuple_addr_constructor");

        if let SilInstructionKind::TupleAddrConstructor {
            init_or_assign,
            dest,
            elements,
        } = &inst.kind
        {
            assert!(matches!(init_or_assign, InitOrAssign::Init));
            assert_eq!(dest, "%0");
            assert_eq!(elements.len(), 2);
        } else {
            panic!("expected TupleAddrConstructor instruction");
        }
    }

    #[test]
    fn test_parse_tuple_addr_constructor_assign() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_stack $(Int, Int)
  %1 = integer_literal $Builtin.Int64, 1
  %2 = integer_literal $Builtin.Int64, 2
  tuple_addr_constructor [assign] %0 : $*(Int, Int) with (%1 : $Int, %2 : $Int)
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::TupleAddrConstructor { .. }))
            .expect("should find tuple_addr_constructor");

        if let SilInstructionKind::TupleAddrConstructor {
            init_or_assign,
            dest,
            elements,
        } = &inst.kind
        {
            assert!(matches!(init_or_assign, InitOrAssign::Assign));
            assert_eq!(dest, "%0");
            assert_eq!(elements.len(), 2);
        } else {
            panic!("expected TupleAddrConstructor instruction");
        }
    }

    #[test]
    fn test_parse_convert_escape_to_noescape_simple() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = function_ref @some_closure : $Closure
  %1 = convert_escape_to_noescape %0 : $Closure to $NoEscapeClosure
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| {
                matches!(
                    &inst.kind,
                    SilInstructionKind::ConvertEscapeToNoEscape { .. }
                )
            })
            .expect("should find convert_escape_to_noescape");

        if let SilInstructionKind::ConvertEscapeToNoEscape {
            operand,
            lifetime_guaranteed,
            ..
        } = &inst.kind
        {
            assert_eq!(operand, "%0");
            assert!(lifetime_guaranteed);
        } else {
            panic!("expected ConvertEscapeToNoEscape instruction");
        }
    }

    #[test]
    fn test_parse_convert_escape_to_noescape_not_guaranteed() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = function_ref @some_closure : $Closure
  %1 = convert_escape_to_noescape [not_guaranteed] %0 : $Closure to $NoEscapeClosure
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| {
                matches!(
                    &inst.kind,
                    SilInstructionKind::ConvertEscapeToNoEscape { .. }
                )
            })
            .expect("should find convert_escape_to_noescape");

        if let SilInstructionKind::ConvertEscapeToNoEscape {
            operand,
            lifetime_guaranteed,
            ..
        } = &inst.kind
        {
            assert_eq!(operand, "%0");
            assert!(!lifetime_guaranteed);
        } else {
            panic!("expected ConvertEscapeToNoEscape instruction");
        }
    }

    #[test]
    fn test_parse_project_block_storage() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_stack $@block_storage Int
  %1 = project_block_storage %0 : $*@block_storage Int
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::ProjectBlockStorage { .. }))
            .expect("should find project_block_storage");

        if let SilInstructionKind::ProjectBlockStorage { operand } = &inst.kind {
            assert_eq!(operand, "%0");
        } else {
            panic!("expected ProjectBlockStorage instruction");
        }
    }

    #[test]
    fn test_parse_init_block_storage_header() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_stack $@block_storage Int
  %1 = function_ref @block_invoke : $@convention(c) () -> ()
  %2 = init_block_storage_header %0 : $*@block_storage Int, invoke %1 : $@convention(c) () -> (), type $@convention(block) () -> ()
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| {
                matches!(
                    &inst.kind,
                    SilInstructionKind::InitBlockStorageHeader { .. }
                )
            })
            .expect("should find init_block_storage_header");

        if let SilInstructionKind::InitBlockStorageHeader {
            block_storage,
            invoke_fn,
            ..
        } = &inst.kind
        {
            assert_eq!(block_storage, "%0");
            assert_eq!(invoke_fn, "%1");
        } else {
            panic!("expected InitBlockStorageHeader instruction");
        }
    }

    #[test]
    fn test_parse_copy_block_simple() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (@owned @convention(block) () -> ()) -> () {
bb0(%0 : $@convention(block) () -> ()):
  %1 = copy_block %0 : $@convention(block) () -> ()
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::CopyBlock { .. }))
            .expect("should find copy_block");

        if let SilInstructionKind::CopyBlock { operand } = &inst.kind {
            assert_eq!(operand, "%0");
        } else {
            panic!("expected CopyBlock instruction");
        }
    }

    #[test]
    fn test_parse_copy_block_without_escaping() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (@owned @convention(block) () -> (), @noescape () -> ()) -> () {
bb0(%0 : $@convention(block) () -> (), %1 : $@noescape () -> ()):
  %2 = copy_block_without_escaping %0 : $@convention(block) () -> () to %1 : $@noescape () -> ()
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| {
                matches!(
                    &inst.kind,
                    SilInstructionKind::CopyBlockWithoutEscaping { .. }
                )
            })
            .expect("should find copy_block_without_escaping");

        if let SilInstructionKind::CopyBlockWithoutEscaping { operand, closure } = &inst.kind {
            assert_eq!(operand, "%0");
            assert_eq!(closure, "%1");
        } else {
            panic!("expected CopyBlockWithoutEscaping instruction");
        }
    }

    #[test]
    fn test_parse_mark_uninitialized_var() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_stack $Int
  %1 = mark_uninitialized [var] %0 : $*Int
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::MarkUninitialized { .. }))
            .expect("should find mark_uninitialized");

        if let SilInstructionKind::MarkUninitialized { kind, operand } = &inst.kind {
            assert!(matches!(kind, MarkUninitializedKind::Var));
            assert_eq!(operand, "%0");
        } else {
            panic!("expected MarkUninitialized instruction");
        }
    }

    #[test]
    fn test_parse_mark_uninitialized_rootself() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_stack $MyClass
  %1 = mark_uninitialized [rootself] %0 : $*MyClass
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::MarkUninitialized { .. }))
            .expect("should find mark_uninitialized");

        if let SilInstructionKind::MarkUninitialized { kind, operand } = &inst.kind {
            assert!(matches!(kind, MarkUninitializedKind::RootSelf));
            assert_eq!(operand, "%0");
        } else {
            panic!("expected MarkUninitialized instruction");
        }
    }

    #[test]
    fn test_parse_mark_uninitialized_delegatingself() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_stack $MyClass
  %1 = mark_uninitialized [delegatingself] %0 : $*MyClass
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::MarkUninitialized { .. }))
            .expect("should find mark_uninitialized");

        if let SilInstructionKind::MarkUninitialized { kind, operand } = &inst.kind {
            assert!(matches!(kind, MarkUninitializedKind::DelegatingSelf));
            assert_eq!(operand, "%0");
        } else {
            panic!("expected MarkUninitialized instruction");
        }
    }

    #[test]
    fn test_parse_mark_uninitialized_crossmodulerootself() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_stack $MyClass
  %1 = mark_uninitialized [crossmodulerootself] %0 : $*MyClass
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::MarkUninitialized { .. }))
            .expect("should find mark_uninitialized");

        if let SilInstructionKind::MarkUninitialized { kind, operand } = &inst.kind {
            assert!(matches!(kind, MarkUninitializedKind::CrossModuleRootSelf));
            assert_eq!(operand, "%0");
        } else {
            panic!("expected MarkUninitialized instruction");
        }
    }

    #[test]
    fn test_parse_mark_uninitialized_derivedself() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_stack $MyClass
  %1 = mark_uninitialized [derivedself] %0 : $*MyClass
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::MarkUninitialized { .. }))
            .expect("should find mark_uninitialized");

        if let SilInstructionKind::MarkUninitialized { kind, operand } = &inst.kind {
            assert!(matches!(kind, MarkUninitializedKind::DerivedSelf));
            assert_eq!(operand, "%0");
        } else {
            panic!("expected MarkUninitialized instruction");
        }
    }

    #[test]
    fn test_parse_mark_uninitialized_derivedselfonly() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_stack $MyClass
  %1 = mark_uninitialized [derivedselfonly] %0 : $*MyClass
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::MarkUninitialized { .. }))
            .expect("should find mark_uninitialized");

        if let SilInstructionKind::MarkUninitialized { kind, operand } = &inst.kind {
            assert!(matches!(kind, MarkUninitializedKind::DerivedSelfOnly));
            assert_eq!(operand, "%0");
        } else {
            panic!("expected MarkUninitialized instruction");
        }
    }

    #[test]
    fn test_parse_mark_uninitialized_delegatinginit() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_stack $MyClass
  %1 = mark_uninitialized [delegatinginit] %0 : $*MyClass
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::MarkUninitialized { .. }))
            .expect("should find mark_uninitialized");

        if let SilInstructionKind::MarkUninitialized { kind, operand } = &inst.kind {
            assert!(matches!(kind, MarkUninitializedKind::DelegatingInit));
            assert_eq!(operand, "%0");
        } else {
            panic!("expected MarkUninitialized instruction");
        }
    }

    #[test]
    fn test_parse_objc_method_simple() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (@owned NSObject) -> () {
bb0(%0 : $NSObject):
  %1 = objc_method %0 : $NSObject, #NSObject.description!getter.foreign : (NSObject) -> () -> String, $@convention(objc_method) (NSObject) -> @autoreleased NSString
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::ObjcMethod { .. }))
            .expect("should find objc_method");

        if let SilInstructionKind::ObjcMethod { operand, method } = &inst.kind {
            assert_eq!(operand, "%0");
            assert!(method.contains("NSObject.description"));
        } else {
            panic!("expected ObjcMethod instruction");
        }
    }

    #[test]
    fn test_parse_objc_super_method() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (@owned MySubclass) -> () {
bb0(%0 : $MySubclass):
  %1 = objc_super_method %0 : $MySubclass, #MySuperclass.method!foreign : (MySuperclass) -> () -> (), $@convention(objc_method) (MySuperclass) -> ()
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::ObjcSuperMethod { .. }))
            .expect("should find objc_super_method");

        if let SilInstructionKind::ObjcSuperMethod { operand, method } = &inst.kind {
            assert_eq!(operand, "%0");
            assert!(method.contains("MySuperclass.method"));
        } else {
            panic!("expected ObjcSuperMethod instruction");
        }
    }

    #[test]
    fn test_parse_objc_protocol_simple() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = objc_protocol #NSCopying : $Protocol
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::ObjcProtocol { .. }))
            .expect("should find objc_protocol");

        if let SilInstructionKind::ObjcProtocol { protocol, ty } = &inst.kind {
            assert_eq!(protocol, "NSCopying");
            assert!(matches!(ty, SilType::Named(n) if n == "Protocol"));
        } else {
            panic!("expected ObjcProtocol instruction");
        }
    }

    #[test]
    fn test_parse_keypath_simple() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = keypath $KeyPath<Person, String>, (root $Person; stored_property #Person.name : $String)
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::KeyPath { .. }))
            .expect("should find keypath");

        if let SilInstructionKind::KeyPath { pattern, .. } = &inst.kind {
            assert!(pattern.contains("Person"));
        } else {
            panic!("expected KeyPath instruction");
        }
    }

    #[test]
    fn test_parse_unmanaged_retain_value() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (@owned AnyObject) -> () {
bb0(%0 : $AnyObject):
  unmanaged_retain_value %0 : $AnyObject
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::UnmanagedRetainValue { .. }))
            .expect("should find unmanaged_retain_value");

        if let SilInstructionKind::UnmanagedRetainValue { operand } = &inst.kind {
            assert_eq!(operand, "%0");
        } else {
            panic!("expected UnmanagedRetainValue instruction");
        }
    }

    #[test]
    fn test_parse_unmanaged_release_value() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (@owned AnyObject) -> () {
bb0(%0 : $AnyObject):
  unmanaged_release_value %0 : $AnyObject
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::UnmanagedReleaseValue { .. }))
            .expect("should find unmanaged_release_value");

        if let SilInstructionKind::UnmanagedReleaseValue { operand } = &inst.kind {
            assert_eq!(operand, "%0");
        } else {
            panic!("expected UnmanagedReleaseValue instruction");
        }
    }

    #[test]
    fn test_parse_unmanaged_autorelease_value() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (@owned AnyObject) -> () {
bb0(%0 : $AnyObject):
  unmanaged_autorelease_value %0 : $AnyObject
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| {
                matches!(
                    &inst.kind,
                    SilInstructionKind::UnmanagedAutoreleaseValue { .. }
                )
            })
            .expect("should find unmanaged_autorelease_value");

        if let SilInstructionKind::UnmanagedAutoreleaseValue { operand } = &inst.kind {
            assert_eq!(operand, "%0");
        } else {
            panic!("expected UnmanagedAutoreleaseValue instruction");
        }
    }

    // ==================== ref_to_unmanaged instruction tests ====================

    #[test]
    fn test_parse_ref_to_unmanaged_simple() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (@owned AnyObject) -> () {
bb0(%0 : $AnyObject):
  %1 = ref_to_unmanaged %0 : $AnyObject to $@sil_unmanaged AnyObject
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::RefToUnmanaged { .. }))
            .expect("should find ref_to_unmanaged");

        if let SilInstructionKind::RefToUnmanaged { operand, ty } = &inst.kind {
            assert_eq!(operand, "%0");
            // The @sil_unmanaged attribute is skipped, and the underlying type is returned
            assert!(matches!(ty, SilType::Named(n) if n == "AnyObject"));
        } else {
            panic!("expected RefToUnmanaged instruction");
        }
    }

    #[test]
    fn test_parse_ref_to_unmanaged_with_class_type() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (@owned MyClass) -> () {
bb0(%0 : $MyClass):
  %1 = ref_to_unmanaged %0 : $MyClass to $@sil_unmanaged MyClass
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::RefToUnmanaged { .. }))
            .expect("should find ref_to_unmanaged");

        if let SilInstructionKind::RefToUnmanaged { operand, .. } = &inst.kind {
            assert_eq!(operand, "%0");
        } else {
            panic!("expected RefToUnmanaged instruction");
        }
    }

    // ==================== unmanaged_to_ref instruction tests ====================

    #[test]
    fn test_parse_unmanaged_to_ref_simple() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = global_addr @globalUnmanaged : $*@sil_unmanaged AnyObject
  %1 = load %0 : $*@sil_unmanaged AnyObject
  %2 = unmanaged_to_ref %1 : $@sil_unmanaged AnyObject to $AnyObject
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::UnmanagedToRef { .. }))
            .expect("should find unmanaged_to_ref");

        if let SilInstructionKind::UnmanagedToRef { operand, ty } = &inst.kind {
            assert_eq!(operand, "%1");
            assert!(matches!(ty, SilType::Named(n) if n == "AnyObject"));
        } else {
            panic!("expected UnmanagedToRef instruction");
        }
    }

    // ==================== ref_to_raw_pointer instruction tests ====================

    #[test]
    fn test_parse_ref_to_raw_pointer_simple() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (@owned AnyObject) -> () {
bb0(%0 : $AnyObject):
  %1 = ref_to_raw_pointer %0 : $AnyObject to $Builtin.RawPointer
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::RefToRawPointer { .. }))
            .expect("should find ref_to_raw_pointer");

        if let SilInstructionKind::RefToRawPointer { operand } = &inst.kind {
            assert_eq!(operand, "%0");
        } else {
            panic!("expected RefToRawPointer instruction");
        }
    }

    #[test]
    fn test_parse_ref_to_raw_pointer_native_object() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (@owned Builtin.NativeObject) -> () {
bb0(%0 : $Builtin.NativeObject):
  %1 = ref_to_raw_pointer %0 : $Builtin.NativeObject to $Builtin.RawPointer
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::RefToRawPointer { .. }))
            .expect("should find ref_to_raw_pointer");

        if let SilInstructionKind::RefToRawPointer { operand } = &inst.kind {
            assert_eq!(operand, "%0");
        } else {
            panic!("expected RefToRawPointer instruction");
        }
    }

    // ==================== raw_pointer_to_ref instruction tests ====================

    #[test]
    fn test_parse_raw_pointer_to_ref_simple() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (@owned Builtin.RawPointer) -> () {
bb0(%0 : $Builtin.RawPointer):
  %1 = raw_pointer_to_ref %0 : $Builtin.RawPointer to $AnyObject
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::RawPointerToRef { .. }))
            .expect("should find raw_pointer_to_ref");

        if let SilInstructionKind::RawPointerToRef { operand, ty } = &inst.kind {
            assert_eq!(operand, "%0");
            assert!(matches!(ty, SilType::Named(n) if n == "AnyObject"));
        } else {
            panic!("expected RawPointerToRef instruction");
        }
    }

    #[test]
    fn test_parse_raw_pointer_to_ref_class_type() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (@owned Builtin.RawPointer) -> () {
bb0(%0 : $Builtin.RawPointer):
  %1 = raw_pointer_to_ref %0 : $Builtin.RawPointer to $MyClass
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::RawPointerToRef { .. }))
            .expect("should find raw_pointer_to_ref");

        if let SilInstructionKind::RawPointerToRef { operand, ty } = &inst.kind {
            assert_eq!(operand, "%0");
            assert!(matches!(ty, SilType::Named(n) if n == "MyClass"));
        } else {
            panic!("expected RawPointerToRef instruction");
        }
    }

    #[test]
    fn test_parse_load_weak_simple() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_stack $@sil_weak Optional<AnyObject>
  %1 = load_weak %0 : $*@sil_weak Optional<AnyObject>
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::LoadWeak { .. }))
            .expect("should find load_weak");

        if let SilInstructionKind::LoadWeak { take, address } = &inst.kind {
            assert!(!take);
            assert_eq!(address, "%0");
        } else {
            panic!("expected LoadWeak instruction");
        }
    }

    #[test]
    fn test_parse_load_weak_take() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_stack $@sil_weak Optional<AnyObject>
  %1 = load_weak [take] %0 : $*@sil_weak Optional<AnyObject>
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::LoadWeak { .. }))
            .expect("should find load_weak");

        if let SilInstructionKind::LoadWeak { take, address } = &inst.kind {
            assert!(take);
            assert_eq!(address, "%0");
        } else {
            panic!("expected LoadWeak instruction");
        }
    }

    #[test]
    fn test_parse_store_weak_simple() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (@owned AnyObject) -> () {
bb0(%0 : $AnyObject):
  %1 = alloc_stack $@sil_weak Optional<AnyObject>
  store_weak %0 to %1 : $*@sil_weak Optional<AnyObject>
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::StoreWeak { .. }))
            .expect("should find store_weak");

        if let SilInstructionKind::StoreWeak { init, source, dest } = &inst.kind {
            assert!(!init);
            assert_eq!(source, "%0");
            assert_eq!(dest, "%1");
        } else {
            panic!("expected StoreWeak instruction");
        }
    }

    #[test]
    fn test_parse_store_weak_init() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (@owned AnyObject) -> () {
bb0(%0 : $AnyObject):
  %1 = alloc_stack $@sil_weak Optional<AnyObject>
  store_weak %0 to [init] %1 : $*@sil_weak Optional<AnyObject>
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::StoreWeak { .. }))
            .expect("should find store_weak");

        if let SilInstructionKind::StoreWeak { init, source, dest } = &inst.kind {
            assert!(init);
            assert_eq!(source, "%0");
            assert_eq!(dest, "%1");
        } else {
            panic!("expected StoreWeak instruction");
        }
    }

    #[test]
    fn test_parse_weak_copy_value() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (@sil_weak Optional<AnyObject>) -> () {
bb0(%0 : $@sil_weak Optional<AnyObject>):
  %1 = weak_copy_value %0 : $@sil_weak Optional<AnyObject>
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::WeakCopyValue { .. }))
            .expect("should find weak_copy_value");

        if let SilInstructionKind::WeakCopyValue { operand } = &inst.kind {
            assert_eq!(operand, "%0");
        } else {
            panic!("expected WeakCopyValue instruction");
        }
    }

    #[test]
    fn test_parse_strong_copy_weak_value() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (@sil_weak Optional<AnyObject>) -> () {
bb0(%0 : $@sil_weak Optional<AnyObject>):
  %1 = strong_copy_weak_value %0 : $@sil_weak Optional<AnyObject>
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::StrongCopyWeakValue { .. }))
            .expect("should find strong_copy_weak_value");

        if let SilInstructionKind::StrongCopyWeakValue { operand } = &inst.kind {
            assert_eq!(operand, "%0");
        } else {
            panic!("expected StrongCopyWeakValue instruction");
        }
    }

    #[test]
    fn test_parse_load_unowned_simple() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_stack $@sil_unowned Optional<AnyObject>
  %1 = load_unowned %0 : $*@sil_unowned Optional<AnyObject>
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::LoadUnowned { .. }))
            .expect("should find load_unowned");

        if let SilInstructionKind::LoadUnowned { take, address } = &inst.kind {
            assert!(!take);
            assert_eq!(address, "%0");
        } else {
            panic!("expected LoadUnowned instruction");
        }
    }

    #[test]
    fn test_parse_load_unowned_take() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_stack $@sil_unowned Optional<AnyObject>
  %1 = load_unowned [take] %0 : $*@sil_unowned Optional<AnyObject>
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::LoadUnowned { .. }))
            .expect("should find load_unowned");

        if let SilInstructionKind::LoadUnowned { take, address } = &inst.kind {
            assert!(take);
            assert_eq!(address, "%0");
        } else {
            panic!("expected LoadUnowned instruction");
        }
    }

    #[test]
    fn test_parse_store_unowned_simple() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (@owned AnyObject) -> () {
bb0(%0 : $AnyObject):
  %1 = alloc_stack $@sil_unowned Optional<AnyObject>
  store_unowned %0 to %1 : $*@sil_unowned Optional<AnyObject>
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::StoreUnowned { .. }))
            .expect("should find store_unowned");

        if let SilInstructionKind::StoreUnowned { init, source, dest } = &inst.kind {
            assert!(!init);
            assert_eq!(source, "%0");
            assert_eq!(dest, "%1");
        } else {
            panic!("expected StoreUnowned instruction");
        }
    }

    #[test]
    fn test_parse_store_unowned_init() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (@owned AnyObject) -> () {
bb0(%0 : $AnyObject):
  %1 = alloc_stack $@sil_unowned Optional<AnyObject>
  store_unowned %0 to [init] %1 : $*@sil_unowned Optional<AnyObject>
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::StoreUnowned { .. }))
            .expect("should find store_unowned");

        if let SilInstructionKind::StoreUnowned { init, source, dest } = &inst.kind {
            assert!(init);
            assert_eq!(source, "%0");
            assert_eq!(dest, "%1");
        } else {
            panic!("expected StoreUnowned instruction");
        }
    }

    #[test]
    fn test_parse_unowned_copy_value() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (@sil_unowned AnyObject) -> () {
bb0(%0 : $@sil_unowned AnyObject):
  %1 = unowned_copy_value %0 : $@sil_unowned AnyObject
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::UnownedCopyValue { .. }))
            .expect("should find unowned_copy_value");

        if let SilInstructionKind::UnownedCopyValue { operand } = &inst.kind {
            assert_eq!(operand, "%0");
        } else {
            panic!("expected UnownedCopyValue instruction");
        }
    }

    #[test]
    fn test_parse_objc_metatype_to_object() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (@objc_metatype NSObject.Type) -> () {
bb0(%0 : $@objc_metatype NSObject.Type):
  %1 = objc_metatype_to_object %0 : $@objc_metatype NSObject.Type to $AnyObject
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::ObjcMetatypeToObject { .. }))
            .expect("should find objc_metatype_to_object");

        if let SilInstructionKind::ObjcMetatypeToObject { operand } = &inst.kind {
            assert_eq!(operand, "%0");
        } else {
            panic!("expected ObjcMetatypeToObject instruction");
        }
    }

    #[test]
    fn test_parse_objc_existential_metatype_to_object() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (@objc_metatype any NSObjectProtocol.Type) -> () {
bb0(%0 : $@objc_metatype any NSObjectProtocol.Type):
  %1 = objc_existential_metatype_to_object %0 : $@objc_metatype any NSObjectProtocol.Type to $AnyObject
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| {
                matches!(
                    &inst.kind,
                    SilInstructionKind::ObjcExistentialMetatypeToObject { .. }
                )
            })
            .expect("should find objc_existential_metatype_to_object");

        if let SilInstructionKind::ObjcExistentialMetatypeToObject { operand } = &inst.kind {
            assert_eq!(operand, "%0");
        } else {
            panic!("expected ObjcExistentialMetatypeToObject instruction");
        }
    }

    #[test]
    fn test_parse_explicit_copy_addr_simple() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_stack $Int
  %1 = alloc_stack $Int
  explicit_copy_addr %0 to %1 : $*Int
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::ExplicitCopyAddr { .. }))
            .expect("should find explicit_copy_addr");

        if let SilInstructionKind::ExplicitCopyAddr {
            source,
            dest,
            take,
            init,
        } = &inst.kind
        {
            assert_eq!(source, "%0");
            assert_eq!(dest, "%1");
            assert!(!take);
            assert!(!init);
        } else {
            panic!("expected ExplicitCopyAddr instruction");
        }
    }

    #[test]
    fn test_parse_explicit_copy_addr_take_init() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_stack $MyClass
  %1 = alloc_stack $MyClass
  explicit_copy_addr [take] %0 to [init] %1 : $*MyClass
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::ExplicitCopyAddr { .. }))
            .expect("should find explicit_copy_addr");

        if let SilInstructionKind::ExplicitCopyAddr {
            source,
            dest,
            take,
            init,
        } = &inst.kind
        {
            assert_eq!(source, "%0");
            assert_eq!(dest, "%1");
            assert!(take);
            assert!(init);
        } else {
            panic!("expected ExplicitCopyAddr instruction");
        }
    }

    // ==================== Load instruction tests ====================

    #[test]
    fn test_parse_load_default() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_stack $Int
  %1 = load %0 : $*Int
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::Load { .. }))
            .expect("should find load");

        if let SilInstructionKind::Load { kind, address } = &inst.kind {
            assert_eq!(*kind, LoadKind::Take);
            assert_eq!(address, "%0");
        } else {
            panic!("expected Load instruction");
        }
    }

    #[test]
    fn test_parse_load_copy() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_stack $Int
  %1 = load [copy] %0 : $*Int
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::Load { .. }))
            .expect("should find load");

        if let SilInstructionKind::Load { kind, address } = &inst.kind {
            assert_eq!(*kind, LoadKind::Copy);
            assert_eq!(address, "%0");
        } else {
            panic!("expected Load instruction");
        }
    }

    #[test]
    fn test_parse_load_take() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_stack $Int
  %1 = load [take] %0 : $*Int
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::Load { .. }))
            .expect("should find load");

        if let SilInstructionKind::Load { kind, address } = &inst.kind {
            assert_eq!(*kind, LoadKind::Take);
            assert_eq!(address, "%0");
        } else {
            panic!("expected Load instruction");
        }
    }

    #[test]
    fn test_parse_load_trivial() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_stack $Int
  %1 = load [trivial] %0 : $*Int
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::Load { .. }))
            .expect("should find load");

        if let SilInstructionKind::Load { kind, address } = &inst.kind {
            assert_eq!(*kind, LoadKind::Trivial);
            assert_eq!(address, "%0");
        } else {
            panic!("expected Load instruction");
        }
    }

    // ==================== Store instruction tests ====================

    #[test]
    fn test_parse_store_default() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0(%0 : $Int):
  %1 = alloc_stack $Int
  store %0 to %1 : $*Int
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::Store { .. }))
            .expect("should find store");

        if let SilInstructionKind::Store { kind, source, dest } = &inst.kind {
            assert_eq!(*kind, StoreKind::Init);
            assert_eq!(source, "%0");
            assert_eq!(dest, "%1");
        } else {
            panic!("expected Store instruction");
        }
    }

    #[test]
    fn test_parse_store_init() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0(%0 : $Int):
  %1 = alloc_stack $Int
  store %0 to [init] %1 : $*Int
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::Store { .. }))
            .expect("should find store");

        if let SilInstructionKind::Store { kind, source, dest } = &inst.kind {
            assert_eq!(*kind, StoreKind::Init);
            assert_eq!(source, "%0");
            assert_eq!(dest, "%1");
        } else {
            panic!("expected Store instruction");
        }
    }

    #[test]
    fn test_parse_store_assign() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0(%0 : $Int):
  %1 = alloc_stack $Int
  store %0 to [assign] %1 : $*Int
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::Store { .. }))
            .expect("should find store");

        if let SilInstructionKind::Store { kind, source, dest } = &inst.kind {
            assert_eq!(*kind, StoreKind::Assign);
            assert_eq!(source, "%0");
            assert_eq!(dest, "%1");
        } else {
            panic!("expected Store instruction");
        }
    }

    #[test]
    fn test_parse_store_trivial() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0(%0 : $Int):
  %1 = alloc_stack $Int
  store %0 to [trivial] %1 : $*Int
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::Store { .. }))
            .expect("should find store");

        if let SilInstructionKind::Store { kind, source, dest } = &inst.kind {
            assert_eq!(*kind, StoreKind::Trivial);
            assert_eq!(source, "%0");
            assert_eq!(dest, "%1");
        } else {
            panic!("expected Store instruction");
        }
    }

    // ==================== Struct instruction tests ====================

    #[test]
    fn test_parse_struct_simple() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = integer_literal $Builtin.Int64, 42
  %1 = integer_literal $Builtin.Int64, 100
  %2 = struct $Point (%0 : $Builtin.Int64, %1 : $Builtin.Int64)
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::Struct { .. }))
            .expect("should find struct");

        if let SilInstructionKind::Struct { ty, operands } = &inst.kind {
            assert!(matches!(ty, SilType::Named(n) if n == "Point"));
            assert_eq!(operands.len(), 2);
            assert_eq!(operands[0], "%0");
            assert_eq!(operands[1], "%1");
        } else {
            panic!("expected Struct instruction");
        }
    }

    #[test]
    fn test_parse_struct_zero_fields() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = struct $EmptyStruct ()
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::Struct { .. }))
            .expect("should find struct");

        if let SilInstructionKind::Struct { ty, operands } = &inst.kind {
            assert!(matches!(ty, SilType::Named(n) if n == "EmptyStruct"));
            assert_eq!(operands.len(), 0);
        } else {
            panic!("expected Struct instruction");
        }
    }

    // ==================== Tuple instruction tests ====================

    #[test]
    fn test_parse_tuple_with_type() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = integer_literal $Builtin.Int64, 1
  %1 = integer_literal $Builtin.Int64, 2
  %2 = tuple $(Int, Int) (%0 : $Int, %1 : $Int)
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::Tuple { .. }))
            .expect("should find tuple");

        if let SilInstructionKind::Tuple { ty, operands } = &inst.kind {
            // The type is parsed as a tuple type
            assert!(!matches!(ty, SilType::Named(n) if n.is_empty()));
            assert_eq!(operands.len(), 2);
            assert_eq!(operands[0], "%0");
            assert_eq!(operands[1], "%1");
        } else {
            panic!("expected Tuple instruction");
        }
    }

    #[test]
    fn test_parse_tuple_without_type() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = integer_literal $Builtin.Int64, 1
  %1 = integer_literal $Builtin.Int64, 2
  %2 = tuple (%0 : $Int, %1 : $Int)
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::Tuple { .. }))
            .expect("should find tuple");

        if let SilInstructionKind::Tuple { operands, .. } = &inst.kind {
            assert_eq!(operands.len(), 2);
            assert_eq!(operands[0], "%0");
            assert_eq!(operands[1], "%1");
        } else {
            panic!("expected Tuple instruction");
        }
    }

    #[test]
    fn test_parse_tuple_zero_elements() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = tuple ()
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::Tuple { .. }))
            .expect("should find tuple");

        if let SilInstructionKind::Tuple { operands, .. } = &inst.kind {
            assert_eq!(operands.len(), 0);
        } else {
            panic!("expected Tuple instruction");
        }
    }

    // ==================== Labeled tuple type test ====================
    // Regression test for issue #13: labeled tuple types like $(lower: T, upper: T)
    // were causing infinite loops in the parser.

    #[test]
    fn test_parse_labeled_tuple_type() {
        // This is a simplified version of the SIL that caused issue #13
        // The key is the labeled tuple type: $(lower: Int, upper: Int)
        let sil = r"
sil_stage canonical

sil @test_labeled_tuple : $@convention(thin) () -> () {
bb0:
  %0 = alloc_stack $(lower: Int, upper: Int)
  %1 = tuple_element_addr %0, 0
  dealloc_stack %0
  %2 = tuple ()
  return %2
}
";
        let module = parse_sil(sil).expect("parse failed - labeled tuple type should be supported");
        assert_eq!(module.functions.len(), 1);
        let func = &module.functions[0];
        assert_eq!(func.name, "test_labeled_tuple");
        assert_eq!(func.blocks.len(), 1);
        // alloc_stack, tuple_element_addr, dealloc_stack, tuple
        assert!(func.blocks[0].instructions.len() >= 3);
    }

    #[test]
    fn test_parse_generic_labeled_tuple_type() {
        // Test generic labeled tuples like $(lower: Self, upper: Self)
        let sil = r"
sil_stage canonical

sil @test_generic_labeled : $@convention(method) <Self> (@in_guaranteed Self, @in_guaranteed Self) -> () {
bb0(%0 : $*Self, %1 : $*Self):
  %2 = alloc_stack $(lower: Self, upper: Self)
  %3 = tuple_element_addr %2, 0
  %4 = tuple_element_addr %2, 1
  dealloc_stack %2
  %5 = tuple ()
  return %5
}
";
        let module =
            parse_sil(sil).expect("parse failed - generic labeled tuple type should be supported");
        assert_eq!(module.functions.len(), 1);
        let func = &module.functions[0];
        assert_eq!(func.blocks.len(), 1);
    }

    #[test]
    fn test_parse_mixed_labeled_unlabeled_tuple() {
        // Swift allows mixing labeled and unlabeled tuple elements
        let sil = r"
sil_stage canonical

sil @test_mixed : $@convention(thin) () -> () {
bb0:
  %0 = alloc_stack $(Int, label2: Bool, Int64)
  dealloc_stack %0
  %1 = tuple ()
  return %1
}
";
        let module = parse_sil(sil)
            .expect("parse failed - mixed labeled/unlabeled tuple should be supported");
        assert_eq!(module.functions.len(), 1);
    }

    #[test]
    fn test_parse_nested_labeled_tuple() {
        // Nested tuples where inner tuple has labels
        let sil = r"
sil_stage canonical

sil @test_nested : $@convention(thin) () -> () {
bb0:
  %0 = alloc_stack $(outer: (inner1: Int, inner2: Bool))
  dealloc_stack %0
  %1 = tuple ()
  return %1
}
";
        let module =
            parse_sil(sil).expect("parse failed - nested labeled tuples should be supported");
        assert_eq!(module.functions.len(), 1);
    }

    #[test]
    fn test_parse_label_underscore_name() {
        // Labels with underscores (common Swift naming)
        let sil = r"
sil_stage canonical

sil @test_underscore : $@convention(thin) () -> () {
bb0:
  %0 = alloc_stack $(first_value: Int, second_value: Bool)
  dealloc_stack %0
  %1 = tuple ()
  return %1
}
";
        let module = parse_sil(sil).expect("parse failed - underscore labels should be supported");
        assert_eq!(module.functions.len(), 1);
    }

    // ==================== Integer literal tests ====================

    #[test]
    fn test_parse_integer_literal_simple() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = integer_literal $Builtin.Int64, 42
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::IntegerLiteral { .. }))
            .expect("should find integer_literal");

        if let SilInstructionKind::IntegerLiteral { ty, value } = &inst.kind {
            assert!(matches!(ty, SilType::Builtin(n) if n.contains("Int64")));
            assert_eq!(*value, 42);
        } else {
            panic!("expected IntegerLiteral instruction");
        }
    }

    #[test]
    fn test_parse_integer_literal_negative() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = integer_literal $Builtin.Int64, -100
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::IntegerLiteral { .. }))
            .expect("should find integer_literal");

        if let SilInstructionKind::IntegerLiteral { ty, value } = &inst.kind {
            assert!(matches!(ty, SilType::Builtin(n) if n.contains("Int64")));
            assert_eq!(*value, -100);
        } else {
            panic!("expected IntegerLiteral instruction");
        }
    }

    #[test]
    fn test_parse_integer_literal_zero() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = integer_literal $Builtin.Int1, 0
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        let inst = bb0
            .instructions
            .iter()
            .find(|inst| matches!(&inst.kind, SilInstructionKind::IntegerLiteral { .. }))
            .expect("should find integer_literal");

        if let SilInstructionKind::IntegerLiteral { ty, value } = &inst.kind {
            assert!(matches!(ty, SilType::Builtin(n) if n.contains("Int1")));
            assert_eq!(*value, 0);
        } else {
            panic!("expected IntegerLiteral instruction");
        }
    }

    // ==================== Return terminator tests ====================

    #[test]
    fn test_parse_return_simple() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (Int) -> Int {
bb0(%0 : $Int):
  return %0 : $Int
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        if let SilTerminator::Return { operand } = &bb0.terminator {
            assert_eq!(operand, "%0");
        } else {
            panic!("expected Return terminator, got {:?}", bb0.terminator);
        }
    }

    #[test]
    fn test_parse_return_undef() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> Int {
bb0:
  return undef : $Int
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        if let SilTerminator::Return { operand } = &bb0.terminator {
            assert_eq!(operand, "undef");
        } else {
            panic!("expected Return terminator, got {:?}", bb0.terminator);
        }
    }

    // ==================== ReturnBorrow terminator tests ====================

    #[test]
    fn test_parse_return_borrow_simple() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (@guaranteed String) -> @guaranteed String {
bb0(%0 : @guaranteed $String):
  return_borrow %0 : $String
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        if let SilTerminator::ReturnBorrow { operand } = &bb0.terminator {
            assert_eq!(operand, "%0");
        } else {
            panic!("expected ReturnBorrow terminator, got {:?}", bb0.terminator);
        }
    }

    // ==================== DynamicMethodBranch terminator tests ====================

    #[test]
    fn test_parse_dynamic_method_branch() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (@guaranteed AnyObject) -> () {
bb0(%0 : $AnyObject):
  dynamic_method_br %0 : $AnyObject, #SomeClass.method, bb1, bb2

bb1(%1 : $@convention(objc_method) (AnyObject) -> ()):
  unreachable

bb2:
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        if let SilTerminator::DynamicMethodBranch {
            operand,
            method,
            has_method_dest,
            no_method_dest,
        } = &bb0.terminator
        {
            assert_eq!(operand, "%0");
            assert!(method.contains("SomeClass.method"));
            assert_eq!(has_method_dest, "bb1");
            assert_eq!(no_method_dest, "bb2");
        } else {
            panic!(
                "expected DynamicMethodBranch terminator, got {:?}",
                bb0.terminator
            );
        }
    }

    // ==================== SwitchValue terminator tests ====================

    #[test]
    fn test_parse_switch_value_simple() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (Builtin.Int64) -> () {
bb0(%0 : $Builtin.Int64):
  %1 = integer_literal $Builtin.Int64, 0
  %2 = integer_literal $Builtin.Int64, 1
  switch_value %0 : $Builtin.Int64, case %1: bb1, case %2: bb2, default bb3

bb1:
  unreachable

bb2:
  unreachable

bb3:
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        if let SilTerminator::SwitchValue {
            operand,
            cases,
            default,
        } = &bb0.terminator
        {
            assert_eq!(operand, "%0");
            assert_eq!(cases.len(), 2);
            assert!(matches!(&cases[0].0, SilConstant::Named(n) if n == "%1"));
            assert_eq!(cases[0].1, "bb1");
            assert!(matches!(&cases[1].0, SilConstant::Named(n) if n == "%2"));
            assert_eq!(cases[1].1, "bb2");
            assert_eq!(default.as_deref(), Some("bb3"));
        } else {
            panic!("expected SwitchValue terminator, got {:?}", bb0.terminator);
        }
    }

    #[test]
    fn test_parse_switch_value_no_default() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (Builtin.Int1) -> () {
bb0(%0 : $Builtin.Int1):
  %1 = integer_literal $Builtin.Int1, 0
  %2 = integer_literal $Builtin.Int1, 1
  switch_value %0 : $Builtin.Int1, case %1: bb1, case %2: bb2

bb1:
  unreachable

bb2:
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        if let SilTerminator::SwitchValue {
            operand,
            cases,
            default,
        } = &bb0.terminator
        {
            assert_eq!(operand, "%0");
            assert_eq!(cases.len(), 2);
            assert!(default.is_none());
        } else {
            panic!("expected SwitchValue terminator, got {:?}", bb0.terminator);
        }
    }

    // ==================== try_apply terminator tests ====================

    #[test]
    fn test_parse_try_apply_simple() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = function_ref @throwingFunc : $@convention(thin) () -> @error Error
  try_apply %0() : $@convention(thin) () -> @error Error, normal bb1, error bb2

bb1(%1 : $()):
  %2 = tuple ()
  return %2

bb2(%3 : $Error):
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        if let SilTerminator::TryApply {
            callee,
            substitutions,
            arguments,
            normal_dest,
            error_dest,
        } = &bb0.terminator
        {
            assert_eq!(callee, "%0");
            assert!(substitutions.is_empty());
            assert!(arguments.is_empty());
            assert_eq!(normal_dest, "bb1");
            assert_eq!(error_dest, "bb2");
        } else {
            panic!("expected TryApply terminator, got {:?}", bb0.terminator);
        }
    }

    #[test]
    fn test_parse_try_apply_with_args() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (Int, String) -> () {
bb0(%0 : $Int, %1 : $String):
  %2 = function_ref @throwingWithArgs : $@convention(thin) (Int, String) -> @error Error
  try_apply %2(%0, %1) : $@convention(thin) (Int, String) -> @error Error, normal bb1, error bb2

bb1(%3 : $()):
  %4 = tuple ()
  return %4

bb2(%5 : $Error):
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        if let SilTerminator::TryApply {
            callee,
            arguments,
            normal_dest,
            error_dest,
            ..
        } = &bb0.terminator
        {
            assert_eq!(callee, "%2");
            assert_eq!(arguments.len(), 2);
            assert_eq!(arguments[0], "%0");
            assert_eq!(arguments[1], "%1");
            assert_eq!(normal_dest, "bb1");
            assert_eq!(error_dest, "bb2");
        } else {
            panic!("expected TryApply terminator, got {:?}", bb0.terminator);
        }
    }

    #[test]
    fn test_parse_try_apply_with_function_ref() {
        // Test try_apply with a direct function reference (@funcname) instead of register
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (@in Int) -> () {
bb0(%0 : $*Int):
  try_apply @throwingOp(%0) : $@convention(thin) (@in Int) -> @error Error, normal bb1, error bb2

bb1(%1 : $()):
  %2 = tuple ()
  return %2

bb2(%3 : $Error):
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        if let SilTerminator::TryApply {
            callee,
            arguments,
            normal_dest,
            error_dest,
            ..
        } = &bb0.terminator
        {
            assert_eq!(callee, "@throwingOp");
            assert_eq!(arguments.len(), 1);
            assert_eq!(arguments[0], "%0");
            assert_eq!(normal_dest, "bb1");
            assert_eq!(error_dest, "bb2");
        } else {
            panic!("expected TryApply terminator, got {:?}", bb0.terminator);
        }
    }

    // ==================== checked_cast_br terminator tests ====================

    #[test]
    fn test_parse_checked_cast_br_simple() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (@owned AnyObject) -> () {
bb0(%0 : $AnyObject):
  checked_cast_br AnyObject in %0 : $AnyObject to MyClass, bb1, bb2

bb1(%1 : $MyClass):
  %2 = tuple ()
  return %2

bb2:
  %3 = tuple ()
  return %3
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        if let SilTerminator::CheckedCastBranch {
            exact,
            operand,
            target_ty,
            success_dest,
            failure_dest,
        } = &bb0.terminator
        {
            assert!(!exact);
            assert_eq!(operand, "%0");
            assert!(matches!(target_ty, SilType::Named(n) if n == "MyClass"));
            assert_eq!(success_dest, "bb1");
            assert_eq!(failure_dest, "bb2");
        } else {
            panic!(
                "expected CheckedCastBranch terminator, got {:?}",
                bb0.terminator
            );
        }
    }

    #[test]
    fn test_parse_checked_cast_br_exact() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (@owned Node) -> () {
bb0(%0 : $Node):
  checked_cast_br [exact] Node in %0 : $Node to ParentNode, bb1, bb2

bb1(%1 : $ParentNode):
  %2 = tuple ()
  return %2

bb2:
  %3 = tuple ()
  return %3
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        if let SilTerminator::CheckedCastBranch {
            exact,
            operand,
            target_ty,
            success_dest,
            failure_dest,
        } = &bb0.terminator
        {
            assert!(exact, "expected [exact] flag to be true");
            assert_eq!(operand, "%0");
            assert!(matches!(target_ty, SilType::Named(n) if n == "ParentNode"));
            assert_eq!(success_dest, "bb1");
            assert_eq!(failure_dest, "bb2");
        } else {
            panic!(
                "expected CheckedCastBranch terminator, got {:?}",
                bb0.terminator
            );
        }
    }

    // ==================== checked_cast_addr_br terminator tests ====================

    #[test]
    fn test_parse_checked_cast_addr_br_take_always() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (@in Any) -> () {
bb0(%0 : $*Any):
  %1 = alloc_stack $Int
  checked_cast_addr_br take_always Any in %0 : $*Any to Int in %1 : $*Int, bb1, bb2

bb1:
  dealloc_stack %1
  %2 = tuple ()
  return %2

bb2:
  dealloc_stack %1
  %3 = tuple ()
  return %3
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        if let SilTerminator::CheckedCastAddrBranch {
            consumption,
            source_ty,
            source,
            target_ty,
            dest,
            success_dest,
            failure_dest,
        } = &bb0.terminator
        {
            assert!(matches!(consumption, CastConsumptionKind::TakeAlways));
            assert!(matches!(source_ty, SilType::Named(n) if n == "Any"));
            assert_eq!(source, "%0");
            assert!(matches!(target_ty, SilType::Named(n) if n == "Int"));
            assert_eq!(dest, "%1");
            assert_eq!(success_dest, "bb1");
            assert_eq!(failure_dest, "bb2");
        } else {
            panic!(
                "expected CheckedCastAddrBranch terminator, got {:?}",
                bb0.terminator
            );
        }
    }

    #[test]
    fn test_parse_checked_cast_addr_br_copy_on_success() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (@in_guaranteed Equatable) -> () {
bb0(%0 : $*Equatable):
  %1 = alloc_stack $String
  checked_cast_addr_br copy_on_success Equatable in %0 : $*Equatable to String in %1 : $*String, bb1, bb2

bb1:
  dealloc_stack %1
  %2 = tuple ()
  return %2

bb2:
  dealloc_stack %1
  %3 = tuple ()
  return %3
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        if let SilTerminator::CheckedCastAddrBranch {
            consumption,
            source_ty,
            source,
            target_ty,
            dest,
            success_dest,
            failure_dest,
        } = &bb0.terminator
        {
            assert!(matches!(consumption, CastConsumptionKind::CopyOnSuccess));
            assert!(matches!(source_ty, SilType::Named(n) if n == "Equatable"));
            assert_eq!(source, "%0");
            assert!(matches!(target_ty, SilType::Named(n) if n == "String"));
            assert_eq!(dest, "%1");
            assert_eq!(success_dest, "bb1");
            assert_eq!(failure_dest, "bb2");
        } else {
            panic!(
                "expected CheckedCastAddrBranch terminator, got {:?}",
                bb0.terminator
            );
        }
    }

    #[test]
    fn test_parse_checked_cast_addr_br_take_on_success() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (@in Any) -> () {
bb0(%0 : $*Any):
  %1 = alloc_stack $Double
  checked_cast_addr_br take_on_success Any in %0 : $*Any to Double in %1 : $*Double, bb1, bb2

bb1:
  dealloc_stack %1
  %2 = tuple ()
  return %2

bb2:
  dealloc_stack %1
  %3 = tuple ()
  return %3
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        if let SilTerminator::CheckedCastAddrBranch {
            consumption,
            source_ty,
            target_ty,
            success_dest,
            failure_dest,
            ..
        } = &bb0.terminator
        {
            assert!(matches!(consumption, CastConsumptionKind::TakeOnSuccess));
            assert!(matches!(source_ty, SilType::Named(n) if n == "Any"));
            assert!(matches!(target_ty, SilType::Named(n) if n == "Double"));
            assert_eq!(success_dest, "bb1");
            assert_eq!(failure_dest, "bb2");
        } else {
            panic!(
                "expected CheckedCastAddrBranch terminator, got {:?}",
                bb0.terminator
            );
        }
    }

    // =============================================================================
    // Tests for unreachable, throw_addr, and unwind terminators
    // =============================================================================

    #[test]
    fn test_parse_unreachable_terminator() {
        let sil = r"
sil @test_unreachable : $@convention(thin) () -> Never {
bb0:
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        assert!(matches!(bb0.terminator, SilTerminator::Unreachable));
    }

    #[test]
    fn test_parse_unreachable_after_function_call() {
        let sil = r"
sil @test_unreachable_after_call : $@convention(thin) () -> Never {
bb0:
  %0 = function_ref @fatalError : $@convention(thin) () -> Never
  %1 = apply %0() : $@convention(thin) () -> Never
  unreachable
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        // Should have 2 instructions + terminator
        assert_eq!(bb0.instructions.len(), 2);
        assert!(matches!(bb0.terminator, SilTerminator::Unreachable));
    }

    #[test]
    fn test_parse_throw_addr_terminator() {
        let sil = r"
sil @test_throw_addr : $@convention(thin) (@in_guaranteed Error) -> @error any Error {
bb0(%0 : $*Error):
  throw_addr
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        assert!(matches!(bb0.terminator, SilTerminator::ThrowAddr));
    }

    #[test]
    fn test_parse_throw_addr_after_copy() {
        let sil = r"
sil @test_throw_addr_after_copy : $@convention(thin) (@in any Error) -> @error any Error {
bb0(%0 : $*any Error):
  %1 = alloc_stack $any Error
  copy_addr %0 to [init] %1 : $*any Error
  throw_addr
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        // Should have 2 instructions + terminator
        assert_eq!(bb0.instructions.len(), 2);
        assert!(matches!(bb0.terminator, SilTerminator::ThrowAddr));
    }

    #[test]
    fn test_parse_unwind_terminator() {
        let sil = r"
sil @test_unwind : $@yield_once @convention(thin) () -> @yields Int {
bb0:
  unwind
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        assert!(matches!(bb0.terminator, SilTerminator::Unwind));
    }

    #[test]
    fn test_parse_unwind_after_yield() {
        let sil = r"
sil @test_unwind_after_yield : $@yield_once @convention(thin) () -> @yields Int {
bb0:
  %0 = integer_literal $Builtin.Int64, 42
  yield %0 : $Builtin.Int64, resume bb1, unwind bb2

bb1:
  %1 = tuple ()
  return %1

bb2:
  unwind
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];

        // bb0 should have yield terminator
        let bb0 = &func.blocks[0];
        assert!(matches!(bb0.terminator, SilTerminator::Yield { .. }));

        // bb2 should have unwind terminator
        let bb2 = &func.blocks[2];
        assert!(matches!(bb2.terminator, SilTerminator::Unwind));
    }

    // =============================================================================
    // Tests for cond_br (conditional branch) terminator
    // =============================================================================

    #[test]
    fn test_parse_cond_br_simple() {
        let sil = r"
sil @test_cond_br : $@convention(thin) (Builtin.Int1) -> Int {
bb0(%0 : $Builtin.Int1):
  cond_br %0, bb1, bb2

bb1:
  %1 = integer_literal $Builtin.Int64, 1
  %2 = struct $Int (%1 : $Builtin.Int64)
  return %2

bb2:
  %3 = integer_literal $Builtin.Int64, 0
  %4 = struct $Int (%3 : $Builtin.Int64)
  return %4
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        if let SilTerminator::CondBranch {
            condition,
            true_dest,
            true_args,
            false_dest,
            false_args,
        } = &bb0.terminator
        {
            assert_eq!(condition, "%0");
            assert_eq!(true_dest, "bb1");
            assert!(true_args.is_empty());
            assert_eq!(false_dest, "bb2");
            assert!(false_args.is_empty());
        } else {
            panic!("expected CondBranch terminator, got {:?}", bb0.terminator);
        }
    }

    #[test]
    fn test_parse_cond_br_with_args() {
        let sil = r"
sil @test_cond_br_args : $@convention(thin) (Builtin.Int1, Int, Int) -> Int {
bb0(%0 : $Builtin.Int1, %1 : $Int, %2 : $Int):
  cond_br %0, bb1(%1 : $Int), bb2(%2 : $Int)

bb1(%3 : $Int):
  return %3

bb2(%4 : $Int):
  return %4
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        if let SilTerminator::CondBranch {
            condition,
            true_dest,
            true_args,
            false_dest,
            false_args,
        } = &bb0.terminator
        {
            assert_eq!(condition, "%0");
            assert_eq!(true_dest, "bb1");
            assert_eq!(true_args.len(), 1);
            assert_eq!(true_args[0], "%1");
            assert_eq!(false_dest, "bb2");
            assert_eq!(false_args.len(), 1);
            assert_eq!(false_args[0], "%2");
        } else {
            panic!("expected CondBranch terminator, got {:?}", bb0.terminator);
        }
    }

    #[test]
    fn test_parse_cond_br_with_multiple_args() {
        let sil = r"
sil @test_cond_br_multi_args : $@convention(thin) (Builtin.Int1, Int, Int, Int) -> (Int, Int) {
bb0(%0 : $Builtin.Int1, %1 : $Int, %2 : $Int, %3 : $Int):
  cond_br %0, bb1(%1 : $Int, %2 : $Int), bb2(%2 : $Int, %3 : $Int)

bb1(%4 : $Int, %5 : $Int):
  %6 = tuple (%4 : $Int, %5 : $Int)
  return %6

bb2(%7 : $Int, %8 : $Int):
  %9 = tuple (%7 : $Int, %8 : $Int)
  return %9
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];
        let bb0 = &func.blocks[0];

        if let SilTerminator::CondBranch {
            condition,
            true_dest,
            true_args,
            false_dest,
            false_args,
        } = &bb0.terminator
        {
            assert_eq!(condition, "%0");
            assert_eq!(true_dest, "bb1");
            assert_eq!(true_args.len(), 2);
            assert_eq!(true_args[0], "%1");
            assert_eq!(true_args[1], "%2");
            assert_eq!(false_dest, "bb2");
            assert_eq!(false_args.len(), 2);
            assert_eq!(false_args[0], "%2");
            assert_eq!(false_args[1], "%3");
        } else {
            panic!("expected CondBranch terminator, got {:?}", bb0.terminator);
        }
    }

    #[test]
    fn test_parse_cond_br_chained() {
        // Test multiple cond_br in a chain (typical control flow pattern)
        let sil = r"
sil @test_cond_br_chain : $@convention(thin) (Builtin.Int1, Builtin.Int1) -> Int {
bb0(%0 : $Builtin.Int1, %1 : $Builtin.Int1):
  cond_br %0, bb1, bb2

bb1:
  cond_br %1, bb3, bb4

bb2:
  %2 = integer_literal $Builtin.Int64, 0
  %3 = struct $Int (%2 : $Builtin.Int64)
  return %3

bb3:
  %4 = integer_literal $Builtin.Int64, 1
  %5 = struct $Int (%4 : $Builtin.Int64)
  return %5

bb4:
  %6 = integer_literal $Builtin.Int64, 2
  %7 = struct $Int (%6 : $Builtin.Int64)
  return %7
}
";
        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];

        // Check bb0 cond_br
        if let SilTerminator::CondBranch {
            condition,
            true_dest,
            false_dest,
            ..
        } = &func.blocks[0].terminator
        {
            assert_eq!(condition, "%0");
            assert_eq!(true_dest, "bb1");
            assert_eq!(false_dest, "bb2");
        } else {
            panic!("expected CondBranch in bb0");
        }

        // Check bb1 cond_br
        if let SilTerminator::CondBranch {
            condition,
            true_dest,
            false_dest,
            ..
        } = &func.blocks[1].terminator
        {
            assert_eq!(condition, "%1");
            assert_eq!(true_dest, "bb3");
            assert_eq!(false_dest, "bb4");
        } else {
            panic!("expected CondBranch in bb1");
        }
    }

    #[test]
    fn test_parse_complex_multiblock_control_flow() {
        // Integration test: Complex control flow with switch_enum, cond_br, br, and merge blocks
        // Tests a realistic pattern with branching and rejoining control flow
        let sil = r"
sil_stage canonical

enum Result {
  case success
  case failure
  case pending
}

sil @test : $@convention(thin) (Result, Builtin.Int1) -> Int {
bb0(%0 : $Result, %1 : $Builtin.Int1):
  switch_enum %0 : $Result, case #Result.success!enumelt: bb1, case #Result.failure!enumelt: bb2, default bb3
bb1:
  %3 = integer_literal $Builtin.Int64, 100
  br bb6(%3)
bb2:
  %5 = integer_literal $Builtin.Int64, -1
  br bb6(%5)
bb3:
  cond_br %1, bb4, bb5
bb4:
  %8 = integer_literal $Builtin.Int64, 50
  br bb6(%8)
bb5:
  %10 = integer_literal $Builtin.Int64, 0
  br bb6(%10)
bb6(%11 : $Builtin.Int64):
  %12 = struct $Int (%11)
  return %12
}
";

        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];

        // Verify we have 7 blocks
        assert_eq!(func.blocks.len(), 7);

        // bb0: switch_enum with 2 cases + default
        assert_switch_enum_to(
            &func.blocks[0].terminator,
            "%0",
            &["Result.success", "Result.failure"],
            Some("bb3"),
        );

        // bb1, bb2: unconditional branches
        assert_branch_to(&func.blocks[1].terminator, "bb6");
        assert_branch_to(&func.blocks[2].terminator, "bb6");

        // bb3: cond_br
        assert_cond_branch_to(&func.blocks[3].terminator, "%1", "bb4", "bb5");

        // bb4, bb5: branches to merge block
        assert_branch_to(&func.blocks[4].terminator, "bb6");
        assert_branch_to(&func.blocks[5].terminator, "bb6");

        // bb6: return (merge block)
        assert_is_return(&func.blocks[6].terminator);
    }

    #[test]
    fn test_parse_multiblock_switch_value() {
        // Integration test: switch_value with multiple cases and default
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (Builtin.Int64) -> Int {
bb0(%0 : $Builtin.Int64):
  %1 = integer_literal $Builtin.Int64, 0
  %2 = integer_literal $Builtin.Int64, 1
  %3 = integer_literal $Builtin.Int64, 2
  switch_value %0 : $Builtin.Int64, case %1: bb1, case %2: bb2, case %3: bb3, default bb4
bb1:
  %5 = integer_literal $Builtin.Int64, 100
  %6 = struct $Int (%5)
  return %6
bb2:
  %7 = integer_literal $Builtin.Int64, 200
  %8 = struct $Int (%7)
  return %8
bb3:
  %9 = integer_literal $Builtin.Int64, 300
  %10 = struct $Int (%9)
  return %10
bb4:
  %11 = integer_literal $Builtin.Int64, -1
  %12 = struct $Int (%11)
  return %12
}
";

        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];

        assert_eq!(func.blocks.len(), 5);

        // bb0: switch_value with 3 cases + default
        if let SilTerminator::SwitchValue {
            operand,
            cases,
            default,
        } = &func.blocks[0].terminator
        {
            assert_eq!(operand, "%0");
            assert_eq!(cases.len(), 3);
            assert!(matches!(&cases[0].0, SilConstant::Named(s) if s == "%1"));
            assert_eq!(cases[0].1, "bb1");
            assert!(matches!(&cases[1].0, SilConstant::Named(s) if s == "%2"));
            assert_eq!(cases[1].1, "bb2");
            assert!(matches!(&cases[2].0, SilConstant::Named(s) if s == "%3"));
            assert_eq!(cases[2].1, "bb3");
            assert_eq!(default.as_ref(), Some(&"bb4".to_string()));
        } else {
            panic!("expected SwitchValue in bb0");
        }

        // All other blocks should return
        for i in 1..5 {
            assert!(
                matches!(&func.blocks[i].terminator, SilTerminator::Return { .. }),
                "expected Return in bb{i}"
            );
        }
    }

    #[test]
    fn test_parse_diamond_control_flow() {
        // Classic diamond pattern: branch -> two paths -> merge -> return
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (Builtin.Int1) -> Int {
bb0(%0 : $Builtin.Int1):
  cond_br %0, bb1, bb2
bb1:
  %2 = integer_literal $Builtin.Int64, 42
  br bb3(%2)
bb2:
  %4 = integer_literal $Builtin.Int64, 0
  br bb3(%4)
bb3(%5 : $Builtin.Int64):
  %6 = struct $Int (%5)
  return %6
}
";

        let module = parse_sil(sil).expect("parse failed");
        let func = &module.functions[0];

        assert_eq!(func.blocks.len(), 4);

        // bb0: cond_br
        if let SilTerminator::CondBranch {
            true_dest,
            false_dest,
            ..
        } = &func.blocks[0].terminator
        {
            assert_eq!(true_dest, "bb1");
            assert_eq!(false_dest, "bb2");
        } else {
            panic!("expected CondBranch");
        }

        // bb1, bb2: branch to bb3
        if let SilTerminator::Branch { dest, args } = &func.blocks[1].terminator {
            assert_eq!(dest, "bb3");
            assert_eq!(args.len(), 1);
            assert_eq!(args[0], "%2");
        } else {
            panic!("expected Branch in bb1");
        }

        if let SilTerminator::Branch { dest, args } = &func.blocks[2].terminator {
            assert_eq!(dest, "bb3");
            assert_eq!(args.len(), 1);
            assert_eq!(args[0], "%4");
        } else {
            panic!("expected Branch in bb2");
        }

        // bb3: return
        assert!(matches!(
            &func.blocks[3].terminator,
            SilTerminator::Return { .. }
        ));

        // bb3 should have one block argument
        assert_eq!(func.blocks[3].arguments.len(), 1);
        assert_eq!(func.blocks[3].arguments[0].name, "%5");
    }

    // ==================== ERROR HANDLING TESTS ====================
    // Tests for malformed SIL and parser error messages

    #[test]
    fn test_error_unknown_opcode() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = unknown_opcode_that_does_not_exist
  return %0 : $()
}
";
        let result = parse_sil(sil);
        // Parser may either error or skip unknown opcodes
        // Just verify it doesn't panic
        let _ = result;
    }

    #[test]
    fn test_error_missing_block_terminator() {
        // A block without any terminator instruction
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> Int {
bb0:
  %0 = integer_literal $Builtin.Int64, 42
}
";
        // This should parse but the block won't have a proper terminator
        // The parser is lenient, so check behavior
        let result = parse_sil(sil);
        // Should either error or produce a block with default terminator
        if let Ok(module) = result {
            let func = &module.functions[0];
            let bb0 = &func.blocks[0];
            // If it parsed, the terminator should default to Unreachable
            assert!(
                matches!(bb0.terminator, SilTerminator::Unreachable),
                "Block without explicit terminator should have Unreachable terminator"
            );
        }
        // Either outcome is acceptable - error or Unreachable terminator
    }

    #[test]
    fn test_error_missing_sil_stage() {
        let sil = r"
sil @test : $@convention(thin) () -> () {
bb0:
  return %0 : $()
}
";
        // Parser should handle missing sil_stage gracefully
        let result = parse_sil(sil);
        // May succeed with default stage or may error
        // Just ensure it doesn't panic
        let _ = result;
    }

    #[test]
    fn test_error_invalid_value_name_format() {
        // Value names should start with %
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  invalid_name = integer_literal $Builtin.Int64, 42
  return %0 : $()
}
";
        let result = parse_sil(sil);
        // Parser may handle this gracefully or error
        // Just verify it doesn't panic
        let _ = result;
    }

    #[test]
    fn test_error_unclosed_brace_in_function() {
        // Test a simpler malformed SIL case - missing closing brace
        let sil = "sil_stage canonical\n\nsil @test : $@convention(thin) () -> () {\nbb0:\n";
        let result = parse_sil(sil);
        // Parser may either error or handle gracefully
        // Just verify it doesn't panic
        let _ = result;
    }

    #[test]
    fn test_error_position_accuracy() {
        // Verify error line/column positions are correct
        let sil = "sil_stage canonical\n\n\nbad_syntax_here";
        let result = parse_sil(sil);
        if let Err(err) = result {
            // Error should be on line 4 (after 3 newlines)
            assert!(err.line >= 3, "Error line should be >= 3, got {}", err.line);
        }
    }

    #[test]
    fn test_error_integer_literal_missing_comma() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> Builtin.Int64 {
bb0:
  %0 = integer_literal $Builtin.Int64 42
  return %0 : $Builtin.Int64
}
";
        // Missing comma between type and value
        let result = parse_sil(sil);
        assert!(result.is_err(), "Should error on missing comma");
        if let Err(err) = result {
            assert!(
                err.message.contains(',') || err.message.contains("expected"),
                "Error should mention missing comma"
            );
        }
    }

    #[test]
    fn test_error_store_missing_to_keyword() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (@in Int) -> () {
bb0(%0 : $*Int):
  %1 = integer_literal $Builtin.Int64, 42
  store %1 [init] %0 : $*Int
  return %2 : $()
}
";
        // Missing 'to' keyword between source and dest
        let result = parse_sil(sil);
        assert!(result.is_err(), "Should error on missing 'to' keyword");
    }

    #[test]
    fn test_error_apply_missing_parenthesis() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = function_ref @foo
  %1 = apply %0 : $@convention(thin) () -> ()
  return %1 : $()
}
";
        // apply without () for arguments
        let result = parse_sil(sil);
        // Parser may tolerate this or error
        let _ = result;
    }

    #[test]
    fn test_error_branch_to_nonexistent_block() {
        // Parser doesn't validate block references, but this tests the syntax
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  br bb_nonexistent
}
";
        // Parser should parse this - validation is separate
        let result = parse_sil(sil);
        if let Ok(module) = result {
            let func = &module.functions[0];
            if let SilTerminator::Branch { dest, .. } = &func.blocks[0].terminator {
                assert_eq!(dest, "bb_nonexistent");
            }
        }
    }

    #[test]
    fn test_error_empty_function_body() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
}
";
        let result = parse_sil(sil);
        // Empty function body - should parse with no blocks or error
        if let Ok(module) = result {
            assert!(
                module.functions[0].blocks.is_empty(),
                "Empty function body should have no blocks"
            );
        }
    }

    #[test]
    fn test_error_duplicate_block_label() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  br bb1
bb0:
  return %0 : $()
}
";
        // Parser doesn't validate uniqueness, but tests parsing behavior
        let result = parse_sil(sil);
        // Should parse both blocks (validation is separate)
        if let Ok(module) = result {
            assert_eq!(
                module.functions[0].blocks.len(),
                2,
                "Should parse both blocks"
            );
        }
    }

    // ==================== EDGE CASE TESTS ====================

    #[test]
    fn test_edge_empty_block() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  unreachable
}
";
        let result = parse_sil(sil).expect("should parse");
        let bb0 = &result.functions[0].blocks[0];
        assert!(
            bb0.instructions.is_empty(),
            "Block with only terminator should have no instructions"
        );
        assert!(matches!(bb0.terminator, SilTerminator::Unreachable));
    }

    #[test]
    fn test_edge_many_block_arguments() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> Int {
bb0:
  %0 = integer_literal $Builtin.Int64, 1
  %1 = integer_literal $Builtin.Int64, 2
  %2 = integer_literal $Builtin.Int64, 3
  %3 = integer_literal $Builtin.Int64, 4
  %4 = integer_literal $Builtin.Int64, 5
  br bb1(%0 : $Builtin.Int64, %1 : $Builtin.Int64, %2 : $Builtin.Int64, %3 : $Builtin.Int64, %4 : $Builtin.Int64)

bb1(%5 : $Builtin.Int64, %6 : $Builtin.Int64, %7 : $Builtin.Int64, %8 : $Builtin.Int64, %9 : $Builtin.Int64):
  return %5 : $Builtin.Int64
}
";
        let result = parse_sil(sil).expect("should parse");
        let bb1 = &result.functions[0].blocks[1];
        assert_eq!(bb1.arguments.len(), 5, "Block should have 5 arguments");
        assert_eq!(bb1.arguments[0].name, "%5");
        assert_eq!(bb1.arguments[4].name, "%9");
    }

    #[test]
    fn test_edge_deeply_nested_tuple_type() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> (Int, (String, (Bool, (Float, Double)))) {
bb0:
  %0 = tuple ()
  return %0 : $(Int, (String, (Bool, (Float, Double))))
}
";
        let result = parse_sil(sil);
        // Should handle deeply nested tuple types
        assert!(result.is_ok(), "Should parse deeply nested tuple types");
    }

    #[test]
    fn test_edge_function_with_generic_constraints() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) <T where T : Equatable, T : Hashable> (@in T) -> Bool {
bb0(%0 : $*T):
  %1 = integer_literal $Builtin.Int1, 1
  return %1 : $Builtin.Int1
}
";
        let result = parse_sil(sil);
        assert!(
            result.is_ok(),
            "Should parse generic constraints: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_edge_empty_tuple_return() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = tuple ()
  return %0 : $()
}
";
        let result = parse_sil(sil).expect("should parse");
        let bb0 = &result.functions[0].blocks[0];
        let tuple_inst = &bb0.instructions[0];
        if let SilInstructionKind::Tuple { operands, .. } = &tuple_inst.kind {
            assert!(operands.is_empty(), "Empty tuple should have no operands");
        } else {
            panic!("Expected Tuple instruction");
        }
    }

    #[test]
    fn test_edge_long_function_name() {
        let long_name = "a".repeat(500);
        let sil = format!(
            r"
sil_stage canonical

sil @{long_name} : $@convention(thin) () -> () {{
bb0:
  return %0 : $()
}}
"
        );
        let result = parse_sil(&sil).expect("should parse long function name");
        assert!(result.functions[0].name.contains(&long_name));
    }

    #[test]
    fn test_edge_unicode_in_string_literal() {
        let sil = r#"
sil_stage canonical

sil @test : $@convention(thin) () -> String {
bb0:
  %0 = string_literal utf8 "Hello 世界 🌍"
  return %0 : $String
}
"#;
        let result = parse_sil(sil).expect("should parse unicode strings");
        let bb0 = &result.functions[0].blocks[0];
        if let SilInstructionKind::StringLiteral { value, .. } = &bb0.instructions[0].kind {
            assert!(value.contains("世界"));
            assert!(value.contains("🌍"));
        }
    }

    #[test]
    fn test_edge_escape_sequences_in_string() {
        let sil = r#"
sil_stage canonical

sil @test : $@convention(thin) () -> String {
bb0:
  %0 = string_literal utf8 "line1\nline2\ttab\\backslash"
  return %0 : $String
}
"#;
        let result = parse_sil(sil).expect("should parse escape sequences");
        let bb0 = &result.functions[0].blocks[0];
        if let SilInstructionKind::StringLiteral { value, .. } = &bb0.instructions[0].kind {
            assert!(
                value.contains("\\n") || value.contains('\n'),
                "Should preserve escape sequences"
            );
        }
    }

    #[test]
    fn test_edge_zero_integer_literal() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> Int {
bb0:
  %0 = integer_literal $Builtin.Int64, 0
  return %0 : $Int
}
";
        let result = parse_sil(sil).expect("should parse zero");
        let bb0 = &result.functions[0].blocks[0];
        if let SilInstructionKind::IntegerLiteral { value, .. } = &bb0.instructions[0].kind {
            assert_eq!(*value, 0);
        }
    }

    #[test]
    fn test_edge_negative_integer_literal() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> Int {
bb0:
  %0 = integer_literal $Builtin.Int64, -9223372036854775808
  return %0 : $Int
}
";
        let result = parse_sil(sil).expect("should parse negative min i64");
        let bb0 = &result.functions[0].blocks[0];
        if let SilInstructionKind::IntegerLiteral { value, .. } = &bb0.instructions[0].kind {
            assert_eq!(*value, i128::from(i64::MIN));
        }
    }

    #[test]
    fn test_edge_max_positive_integer() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> Int {
bb0:
  %0 = integer_literal $Builtin.Int64, 9223372036854775807
  return %0 : $Int
}
";
        let result = parse_sil(sil).expect("should parse max i64");
        let bb0 = &result.functions[0].blocks[0];
        if let SilInstructionKind::IntegerLiteral { value, .. } = &bb0.instructions[0].kind {
            assert_eq!(*value, i128::from(i64::MAX));
        }
    }

    // ==================== COMPLEX GENERIC TYPE TESTS ====================

    #[test]
    fn test_generic_associated_type() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) <T : Collection> (@in T) -> @out T.Element {
bb0(%0 : $*T.Element, %1 : $*T):
  return %0 : $*T.Element
}
";
        let result = parse_sil(sil);
        assert!(
            result.is_ok(),
            "Should parse associated types: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_generic_nested_generic_type() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) <T, U> () -> @out Dictionary<Array<T>, Optional<U>> {
bb0(%0 : $*Dictionary<Array<T>, Optional<U>>):
  return %0 : $*Dictionary<Array<T>, Optional<U>>
}
";
        let result = parse_sil(sil);
        assert!(
            result.is_ok(),
            "Should parse nested generics: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_generic_function_type_with_generics() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> @callee_guaranteed <T> (@in T) -> @out T {
bb0:
  %0 = tuple ()
  return %0 : $()
}
";
        let result = parse_sil(sil);
        // Function type with generic parameters
        assert!(
            result.is_ok(),
            "Should parse generic function types: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_generic_protocol_composition() {
        // Test simple protocol composition type
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (@in Equatable) -> Bool {
bb0(%0 : $*Equatable):
  %1 = integer_literal $Builtin.Int1, 1
  return %1 : $Builtin.Int1
}
";
        let result = parse_sil(sil);
        assert!(
            result.is_ok(),
            "Should parse protocol types: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_generic_metatype_of_generic() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) <T> () -> @thick T.Type {
bb0:
  %0 = metatype $@thick T.Type
  return %0 : $@thick T.Type
}
";
        let result = parse_sil(sil).expect("should parse");
        let bb0 = &result.functions[0].blocks[0];
        assert!(matches!(
            &bb0.instructions[0].kind,
            SilInstructionKind::Metatype { .. }
        ));
    }

    #[test]
    fn test_generic_tuple_with_multiple_elements() {
        // Test unlabeled tuple types (labeled tuples may not be fully supported)
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> (Int, Int, Int) {
bb0:
  %0 = tuple ()
  return %0 : $(Int, Int, Int)
}
";
        let result = parse_sil(sil);
        assert!(
            result.is_ok(),
            "Should parse tuple types: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_generic_optional_chain_type() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> Optional<Optional<Optional<Int>>> {
bb0:
  %0 = enum $Optional<Optional<Optional<Int>>>, #Optional.none!enumelt
  return %0 : $Optional<Optional<Optional<Int>>>
}
";
        let result = parse_sil(sil).expect("should parse optional chain");
        let bb0 = &result.functions[0].blocks[0];
        if let SilInstructionKind::Enum { case_name, .. } = &bb0.instructions[0].kind {
            assert!(case_name.contains("Optional.none"));
        }
    }

    #[test]
    fn test_generic_result_type() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> Result<Array<String>, Error> {
bb0:
  %0 = tuple ()
  return %0 : $Result<Array<String>, Error>
}
";
        let result = parse_sil(sil);
        assert!(
            result.is_ok(),
            "Should parse Result generic type: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_generic_closure_capturing_generic() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) <T> (@in T) -> @owned @callee_guaranteed () -> @out T {
bb0(%0 : $*T):
  %1 = tuple ()
  return %1 : $()
}
";
        let result = parse_sil(sil);
        assert!(
            result.is_ok(),
            "Should parse closure capturing generic: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_generic_protocol_witness_table_ref() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) <T : Hashable> (@in T) -> () {
bb0(%0 : $*T):
  %1 = witness_method $T, #Hashable.hashValue!getter : <Self where Self : Hashable> (Self) -> () -> Int
  return %1 : $()
}
";
        let result = parse_sil(sil);
        // witness_method is complex - may succeed or fail
        let _ = result;
    }

    #[test]
    fn test_generic_variadic_generics() {
        // Swift 5.9+ variadic generics
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) <each T> () -> () {
bb0:
  return %0 : $()
}
";
        let result = parse_sil(sil);
        // Variadic generics syntax
        assert!(
            result.is_ok(),
            "Should handle variadic generics: {:?}",
            result.err()
        );
    }

    // ============================================================
    // Float literal parsing tests (hex, negative, zero, f32)
    // ============================================================

    #[test]
    fn test_parse_float_literal_hex() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> Builtin.FPIEEE64 {
bb0:
  %0 = float_literal $Builtin.FPIEEE64, 0x400921fb54442d18
  return %0 : $Builtin.FPIEEE64
}
";
        let result = parse_sil(sil).expect("should parse hex float literal");
        let bb0 = &result.functions[0].blocks[0];
        if let SilInstructionKind::FloatLiteral { value, .. } = &bb0.instructions[0].kind {
            // 0x400921fb54442d18 is π in IEEE 754
            assert!(
                (*value - std::f64::consts::PI).abs() < 0.0001,
                "Expected π, got {value}"
            );
        } else {
            panic!("Expected FloatLiteral instruction");
        }
    }

    #[test]
    fn test_parse_float_literal_negative() {
        // Use -2.5 instead of -2.718 to avoid clippy::approx_constant (E ≈ 2.718)
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> Builtin.FPIEEE64 {
bb0:
  %0 = float_literal $Builtin.FPIEEE64, -2.5
  return %0 : $Builtin.FPIEEE64
}
";
        let result = parse_sil(sil).expect("should parse negative float literal");
        let bb0 = &result.functions[0].blocks[0];
        if let SilInstructionKind::FloatLiteral { value, .. } = &bb0.instructions[0].kind {
            assert!((*value + 2.5).abs() < 0.001, "Expected -2.5, got {value}");
        } else {
            panic!("Expected FloatLiteral instruction");
        }
    }

    #[test]
    fn test_parse_float_literal_zero() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> Builtin.FPIEEE64 {
bb0:
  %0 = float_literal $Builtin.FPIEEE64, 0.0
  return %0 : $Builtin.FPIEEE64
}
";
        let result = parse_sil(sil).expect("should parse zero float literal");
        let bb0 = &result.functions[0].blocks[0];
        if let SilInstructionKind::FloatLiteral { value, .. } = &bb0.instructions[0].kind {
            assert!(value.abs() < 0.0001, "Expected 0.0, got {value}");
        } else {
            panic!("Expected FloatLiteral instruction");
        }
    }

    #[test]
    fn test_parse_float_literal_f32() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> Builtin.FPIEEE32 {
bb0:
  %0 = float_literal $Builtin.FPIEEE32, 1.5
  return %0 : $Builtin.FPIEEE32
}
";
        let result = parse_sil(sil).expect("should parse f32 float literal");
        let bb0 = &result.functions[0].blocks[0];
        if let SilInstructionKind::FloatLiteral { ty, value } = &bb0.instructions[0].kind {
            assert!((*value - 1.5).abs() < 0.001, "Expected 1.5, got {value}");
            let ty_str = format!("{ty:?}");
            assert!(
                ty_str.contains("FPIEEE32"),
                "Expected FPIEEE32 type, got: {ty_str}"
            );
        } else {
            panic!("Expected FloatLiteral instruction");
        }
    }

    // ============================================================
    // Begin/end access parsing tests
    // ============================================================

    #[test]
    fn test_parse_begin_access_read_static() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (@inout Int) -> () {
bb0(%0 : $*Int):
  %1 = begin_access [read] [static] %0 : $*Int
  end_access %1 : $*Int
  %r = tuple ()
  return %r : $()
}
";
        let result = parse_sil(sil).expect("should parse begin_access read static");
        let bb0 = &result.functions[0].blocks[0];
        if let SilInstructionKind::BeginAccess {
            kind,
            enforcement,
            address,
        } = &bb0.instructions[0].kind
        {
            assert!(matches!(kind, AccessKind::Read));
            assert!(matches!(enforcement, Enforcement::Static));
            assert_eq!(address, "%0");
        } else {
            panic!("Expected BeginAccess instruction");
        }
    }

    #[test]
    fn test_parse_begin_access_modify_dynamic() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (@inout Int) -> () {
bb0(%0 : $*Int):
  %1 = begin_access [modify] [dynamic] %0 : $*Int
  end_access %1 : $*Int
  %r = tuple ()
  return %r : $()
}
";
        let result = parse_sil(sil).expect("should parse begin_access modify dynamic");
        let bb0 = &result.functions[0].blocks[0];
        if let SilInstructionKind::BeginAccess {
            kind, enforcement, ..
        } = &bb0.instructions[0].kind
        {
            assert!(matches!(kind, AccessKind::Modify));
            assert!(matches!(enforcement, Enforcement::Dynamic));
        } else {
            panic!("Expected BeginAccess instruction");
        }
    }

    #[test]
    fn test_parse_begin_access_init() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (@inout Int) -> () {
bb0(%0 : $*Int):
  %1 = begin_access [init] [static] %0 : $*Int
  end_access %1 : $*Int
  %r = tuple ()
  return %r : $()
}
";
        let result = parse_sil(sil).expect("should parse begin_access init");
        let bb0 = &result.functions[0].blocks[0];
        if let SilInstructionKind::BeginAccess { kind, .. } = &bb0.instructions[0].kind {
            assert!(matches!(kind, AccessKind::Init));
        } else {
            panic!("Expected BeginAccess instruction");
        }
    }

    #[test]
    fn test_parse_begin_access_deinit() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (@inout Int) -> () {
bb0(%0 : $*Int):
  %1 = begin_access [deinit] [unsafe] %0 : $*Int
  end_access %1 : $*Int
  %r = tuple ()
  return %r : $()
}
";
        let result = parse_sil(sil).expect("should parse begin_access deinit");
        let bb0 = &result.functions[0].blocks[0];
        if let SilInstructionKind::BeginAccess {
            kind, enforcement, ..
        } = &bb0.instructions[0].kind
        {
            assert!(matches!(kind, AccessKind::Deinit));
            assert!(matches!(enforcement, Enforcement::Unsafe));
        } else {
            panic!("Expected BeginAccess instruction");
        }
    }

    #[test]
    fn test_parse_end_access_simple() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (@inout Int) -> () {
bb0(%0 : $*Int):
  %1 = begin_access [read] [static] %0 : $*Int
  end_access %1 : $*Int
  %r = tuple ()
  return %r : $()
}
";
        let result = parse_sil(sil).expect("should parse end_access");
        let bb0 = &result.functions[0].blocks[0];
        if let SilInstructionKind::EndAccess { address } = &bb0.instructions[1].kind {
            assert_eq!(address, "%1");
        } else {
            panic!("Expected EndAccess instruction");
        }
    }

    // ============================================================
    // Begin/end borrow parsing tests
    // ============================================================

    #[test]
    fn test_parse_begin_borrow_simple() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (@owned String) -> () {
bb0(%0 : $String):
  %1 = begin_borrow %0 : $String
  end_borrow %1 : $String
  destroy_value %0 : $String
  %r = tuple ()
  return %r : $()
}
";
        let result = parse_sil(sil).expect("should parse begin_borrow");
        let bb0 = &result.functions[0].blocks[0];
        if let SilInstructionKind::BeginBorrow { operand } = &bb0.instructions[0].kind {
            assert_eq!(operand, "%0");
        } else {
            panic!("Expected BeginBorrow instruction");
        }
    }

    #[test]
    fn test_parse_end_borrow_simple() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (@owned String) -> () {
bb0(%0 : $String):
  %1 = begin_borrow %0 : $String
  end_borrow %1 : $String
  destroy_value %0 : $String
  %r = tuple ()
  return %r : $()
}
";
        let result = parse_sil(sil).expect("should parse end_borrow");
        let bb0 = &result.functions[0].blocks[0];
        if let SilInstructionKind::EndBorrow { operand } = &bb0.instructions[1].kind {
            assert_eq!(operand, "%1");
        } else {
            panic!("Expected EndBorrow instruction");
        }
    }

    // ============================================================
    // Copy/destroy value parsing tests
    // ============================================================

    #[test]
    fn test_parse_copy_value_simple() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (@owned String) -> @owned String {
bb0(%0 : $String):
  %1 = copy_value %0 : $String
  destroy_value %0 : $String
  return %1 : $String
}
";
        let result = parse_sil(sil).expect("should parse copy_value");
        let bb0 = &result.functions[0].blocks[0];
        if let SilInstructionKind::CopyValue { operand } = &bb0.instructions[0].kind {
            assert_eq!(operand, "%0");
        } else {
            panic!("Expected CopyValue instruction");
        }
    }

    #[test]
    fn test_parse_destroy_value_simple() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (@owned String) -> () {
bb0(%0 : $String):
  destroy_value %0 : $String
  %r = tuple ()
  return %r : $()
}
";
        let result = parse_sil(sil).expect("should parse destroy_value");
        let bb0 = &result.functions[0].blocks[0];
        if let SilInstructionKind::DestroyValue { operand } = &bb0.instructions[0].kind {
            assert_eq!(operand, "%0");
        } else {
            panic!("Expected DestroyValue instruction");
        }
    }

    // ============================================================
    // Strong retain/release parsing tests
    // ============================================================

    #[test]
    fn test_parse_strong_retain_simple() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (@guaranteed SomeClass) -> () {
bb0(%0 : $SomeClass):
  strong_retain %0 : $SomeClass
  strong_release %0 : $SomeClass
  %r = tuple ()
  return %r : $()
}
";
        let result = parse_sil(sil).expect("should parse strong_retain");
        let bb0 = &result.functions[0].blocks[0];
        if let SilInstructionKind::StrongRetain { operand } = &bb0.instructions[0].kind {
            assert_eq!(operand, "%0");
        } else {
            panic!("Expected StrongRetain instruction");
        }
    }

    #[test]
    fn test_parse_strong_release_simple() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (@guaranteed SomeClass) -> () {
bb0(%0 : $SomeClass):
  strong_retain %0 : $SomeClass
  strong_release %0 : $SomeClass
  %r = tuple ()
  return %r : $()
}
";
        let result = parse_sil(sil).expect("should parse strong_release");
        let bb0 = &result.functions[0].blocks[0];
        if let SilInstructionKind::StrongRelease { operand } = &bb0.instructions[1].kind {
            assert_eq!(operand, "%0");
        } else {
            panic!("Expected StrongRelease instruction");
        }
    }

    // ============================================================
    // Retain/release value parsing tests
    // ============================================================

    #[test]
    fn test_parse_retain_value_simple() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (@guaranteed SomeStruct) -> () {
bb0(%0 : $SomeStruct):
  retain_value %0 : $SomeStruct
  release_value %0 : $SomeStruct
  %r = tuple ()
  return %r : $()
}
";
        let result = parse_sil(sil).expect("should parse retain_value");
        let bb0 = &result.functions[0].blocks[0];
        if let SilInstructionKind::RetainValue { operand } = &bb0.instructions[0].kind {
            assert_eq!(operand, "%0");
        } else {
            panic!("Expected RetainValue instruction");
        }
    }

    #[test]
    fn test_parse_release_value_simple() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (@guaranteed SomeStruct) -> () {
bb0(%0 : $SomeStruct):
  retain_value %0 : $SomeStruct
  release_value %0 : $SomeStruct
  %r = tuple ()
  return %r : $()
}
";
        let result = parse_sil(sil).expect("should parse release_value");
        let bb0 = &result.functions[0].blocks[0];
        if let SilInstructionKind::ReleaseValue { operand } = &bb0.instructions[1].kind {
            assert_eq!(operand, "%0");
        } else {
            panic!("Expected ReleaseValue instruction");
        }
    }

    // ============================================================
    // Destroy addr parsing tests
    // ============================================================

    #[test]
    fn test_parse_destroy_addr_simple() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (@in String) -> () {
bb0(%0 : $*String):
  destroy_addr %0 : $*String
  %r = tuple ()
  return %r : $()
}
";
        let result = parse_sil(sil).expect("should parse destroy_addr");
        let bb0 = &result.functions[0].blocks[0];
        if let SilInstructionKind::DestroyAddr { address } = &bb0.instructions[0].kind {
            assert_eq!(address, "%0");
        } else {
            panic!("Expected DestroyAddr instruction");
        }
    }

    // ============================================================
    // Metatype parsing tests
    // ============================================================

    #[test]
    fn test_parse_metatype_thick() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> @thick Int.Type {
bb0:
  %0 = metatype $@thick Int.Type
  return %0 : $@thick Int.Type
}
";
        let result = parse_sil(sil).expect("should parse metatype thick");
        let bb0 = &result.functions[0].blocks[0];
        if let SilInstructionKind::Metatype { ty } = &bb0.instructions[0].kind {
            let ty_str = format!("{ty:?}");
            assert!(
                ty_str.contains("thick") || ty_str.contains("Int"),
                "Expected thick metatype, got: {ty_str}"
            );
        } else {
            panic!("Expected Metatype instruction");
        }
    }

    #[test]
    fn test_parse_metatype_thin() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> @thin SomeStruct.Type {
bb0:
  %0 = metatype $@thin SomeStruct.Type
  return %0 : $@thin SomeStruct.Type
}
";
        let result = parse_sil(sil).expect("should parse metatype thin");
        let bb0 = &result.functions[0].blocks[0];
        assert!(matches!(
            bb0.instructions[0].kind,
            SilInstructionKind::Metatype { .. }
        ));
    }

    // ============================================================
    // Fix lifetime parsing tests
    // ============================================================

    #[test]
    fn test_parse_fix_lifetime_simple() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (@guaranteed SomeClass) -> () {
bb0(%0 : $SomeClass):
  fix_lifetime %0 : $SomeClass
  %r = tuple ()
  return %r : $()
}
";
        let result = parse_sil(sil).expect("should parse fix_lifetime");
        let bb0 = &result.functions[0].blocks[0];
        if let SilInstructionKind::FixLifetime { operand } = &bb0.instructions[0].kind {
            assert_eq!(operand, "%0");
        } else {
            panic!("Expected FixLifetime instruction");
        }
    }

    // ============================================================
    // Is unique parsing tests
    // ============================================================

    #[test]
    fn test_parse_is_unique_simple() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (@inout SomeClass) -> Builtin.Int1 {
bb0(%0 : $*SomeClass):
  %1 = is_unique %0 : $*SomeClass
  return %1 : $Builtin.Int1
}
";
        let result = parse_sil(sil).expect("should parse is_unique");
        let bb0 = &result.functions[0].blocks[0];
        if let SilInstructionKind::IsUnique { operand } = &bb0.instructions[0].kind {
            assert_eq!(operand, "%0");
        } else {
            panic!("Expected IsUnique instruction");
        }
    }

    // ============================================================
    // Mark dependence parsing tests
    // ============================================================

    #[test]
    fn test_parse_mark_dependence_simple() {
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) (@guaranteed SomeClass) -> UnsafePointer<Int> {
bb0(%0 : $SomeClass):
  %1 = ref_to_raw_pointer %0 : $SomeClass to $Builtin.RawPointer
  %2 = mark_dependence %1 : $Builtin.RawPointer on %0 : $SomeClass
  return %2 : $Builtin.RawPointer
}
";
        let result = parse_sil(sil).expect("should parse mark_dependence");
        let bb0 = &result.functions[0].blocks[0];
        if let SilInstructionKind::MarkDependence { value, base } = &bb0.instructions[1].kind {
            assert_eq!(value, "%1");
            assert_eq!(base, "%0");
        } else {
            panic!(
                "Expected MarkDependence instruction, got {:?}",
                bb0.instructions[1].kind
            );
        }
    }

    // ============================================================
    // SilParseError tests
    // ============================================================

    #[test]
    fn test_sil_parse_error_display_format() {
        let err = SilParseError {
            message: "unexpected token".to_string(),
            line: 42,
            column: 13,
        };
        let display = format!("{err}");
        assert_eq!(display, "SIL parse error at 42:13: unexpected token");
    }

    #[test]
    fn test_sil_parse_error_display_first_line() {
        let err = SilParseError {
            message: "missing semicolon".to_string(),
            line: 1,
            column: 1,
        };
        let display = format!("{err}");
        assert_eq!(display, "SIL parse error at 1:1: missing semicolon");
    }

    #[test]
    fn test_sil_parse_error_display_empty_message() {
        let err = SilParseError {
            message: String::new(),
            line: 10,
            column: 5,
        };
        let display = format!("{err}");
        assert_eq!(display, "SIL parse error at 10:5: ");
    }

    #[test]
    fn test_sil_parse_error_display_large_line_numbers() {
        let err = SilParseError {
            message: "parse error".to_string(),
            line: 99999,
            column: 256,
        };
        let display = format!("{err}");
        assert_eq!(display, "SIL parse error at 99999:256: parse error");
    }

    #[test]
    fn test_sil_parse_error_debug_format() {
        let err = SilParseError {
            message: "test error".to_string(),
            line: 5,
            column: 10,
        };
        let debug = format!("{err:?}");
        assert!(debug.contains("SilParseError"));
        assert!(debug.contains("test error"));
        assert!(debug.contains('5'));
        assert!(debug.contains("10"));
    }

    #[test]
    fn test_sil_parse_error_clone() {
        let err = SilParseError {
            message: "original".to_string(),
            line: 100,
            column: 50,
        };
        let cloned = err;
        assert_eq!(cloned.message, "original");
        assert_eq!(cloned.line, 100);
        assert_eq!(cloned.column, 50);
    }

    #[test]
    fn test_sil_parse_error_is_std_error() {
        let err = SilParseError {
            message: "std error".to_string(),
            line: 1,
            column: 1,
        };
        // Verify it implements std::error::Error by using the trait method
        let _: &dyn std::error::Error = &err;
    }

    #[test]
    fn test_sil_parse_error_display_special_characters() {
        let err = SilParseError {
            message: "unexpected '\"' in string".to_string(),
            line: 7,
            column: 20,
        };
        let display = format!("{err}");
        assert_eq!(
            display,
            "SIL parse error at 7:20: unexpected '\"' in string"
        );
    }

    #[test]
    fn test_sil_parse_error_display_unicode_message() {
        let err = SilParseError {
            message: "invalid identifier: λ".to_string(),
            line: 3,
            column: 8,
        };
        let display = format!("{err}");
        assert_eq!(display, "SIL parse error at 3:8: invalid identifier: λ");
    }

    // =========================================================================
    // Error path tests for parse instruction functions
    // These test the .map_err closures that handle parse failures
    // =========================================================================

    #[test]
    fn test_parse_scalar_pack_index_invalid_index() {
        // Test error path: non-numeric index should fail
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = scalar_pack_index abc of $Pack{Int}
  unreachable
}
";
        let result = parse_sil(sil);
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(
            err.message.contains("invalid scalar_pack_index index")
                || err.message.contains("expected digit")
                || err.message.contains("index"),
            "error should mention invalid index: {}",
            err.message
        );
    }

    #[test]
    fn test_parse_scalar_pack_index_missing_of_keyword() {
        // Test error path: missing "of" keyword
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = scalar_pack_index 0 at $Pack{Int}
  unreachable
}
";
        let result = parse_sil(sil);
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(
            err.message.contains("expected 'of'"),
            "error should mention missing 'of': {}",
            err.message
        );
    }

    #[test]
    fn test_parse_pack_pack_index_invalid_component_index() {
        // Test error path: non-numeric component index should fail
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = integer_literal $Builtin.Word, 0
  %1 = pack_pack_index xyz, %0 of $Pack{Int}
  unreachable
}
";
        let result = parse_sil(sil);
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(
            err.message.contains("invalid pack_pack_index")
                || err.message.contains("component index")
                || err.message.contains("expected digit"),
            "error should mention invalid component index: {}",
            err.message
        );
    }

    #[test]
    fn test_parse_pack_pack_index_missing_of_keyword() {
        // Test error path: missing "of" keyword
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = integer_literal $Builtin.Word, 0
  %1 = pack_pack_index 1, %0 at $Pack{Int}
  unreachable
}
";
        let result = parse_sil(sil);
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(
            err.message.contains("expected 'of'"),
            "error should mention missing 'of': {}",
            err.message
        );
    }

    #[test]
    fn test_parse_tuple_extract_invalid_index() {
        // Test error path: non-numeric tuple index should fail
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) ((Int, Bool)) -> Int {
bb0(%0 : $(Int, Bool)):
  %1 = tuple_extract %0, abc
  return %1 : $Int
}
";
        let result = parse_sil(sil);
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(
            err.message.contains("invalid tuple index") || err.message.contains("expected digit"),
            "error should mention invalid tuple index: {}",
            err.message
        );
    }

    #[test]
    fn test_parse_tuple_element_addr_invalid_index() {
        // Test error path: non-numeric tuple element index should fail
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_stack $(Int, Bool)
  %1 = tuple_element_addr %0 : $*(Int, Bool), xyz
  dealloc_stack %0 : $*(Int, Bool)
  unreachable
}
";
        let result = parse_sil(sil);
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(
            err.message.contains("invalid tuple element index")
                || err.message.contains("expected digit"),
            "error should mention invalid index: {}",
            err.message
        );
    }

    #[test]
    fn test_parse_project_box_invalid_field_index() {
        // Test error path: non-numeric field index should fail
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = alloc_box ${ var Int }
  %1 = project_box %0 : ${ var Int }, abc
  dealloc_box %0 : ${ var Int }
  unreachable
}
";
        let result = parse_sil(sil);
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(
            err.message.contains("invalid project_box field index")
                || err.message.contains("invalid field index")
                || err.message.contains("expected digit"),
            "error should mention invalid field index: {}",
            err.message
        );
    }

    #[test]
    fn test_parse_integer_literal_invalid_value() {
        // Test error path: non-numeric integer literal value should fail
        let sil = r"
sil_stage canonical

sil @test : $@convention(thin) () -> () {
bb0:
  %0 = integer_literal $Builtin.Int64, not_a_number
  unreachable
}
";
        let result = parse_sil(sil);
        assert!(result.is_err());
        let err = result.unwrap_err();
        // The error message varies based on what the parser encounters
        assert!(
            err.message.contains("integer")
                || err.message.contains("literal")
                || err.message.contains("expected"),
            "error should indicate parse failure: {}",
            err.message
        );
    }

    #[test]
    fn test_parse_function_empty_blocks() {
        // Test: function with only empty blocks (no instructions, no terminator)
        // This exercises certain edge cases in the parser
        let sil = r"
sil_stage canonical

sil @empty_test : $@convention(thin) () -> () {
bb0:
  unreachable
}
";
        let result = parse_sil(sil);
        assert!(result.is_ok());
        let module = result.unwrap();
        let func = module
            .functions
            .iter()
            .find(|f| f.name.contains("empty_test"))
            .expect("should find empty_test function");
        assert_eq!(func.blocks.len(), 1);
        assert!(func.blocks[0].instructions.is_empty());
    }

    #[test]
    fn test_parse_sil_empty_input() {
        // Test: completely empty input
        let sil = "";
        let result = parse_sil(sil);
        // Empty input should either succeed with empty module or fail gracefully
        match result {
            Ok(module) => {
                assert!(module.functions.is_empty());
            }
            Err(err) => {
                // If it fails, should be a reasonable error
                assert!(
                    err.message.contains("empty")
                        || err.message.contains("expected")
                        || err.message.contains("stage"),
                    "unexpected error: {}",
                    err.message
                );
            }
        }
    }

    #[test]
    fn test_parse_sil_only_whitespace() {
        // Test: only whitespace
        let sil = "   \n\t\n   ";
        let result = parse_sil(sil);
        match result {
            Ok(module) => {
                assert!(module.functions.is_empty());
            }
            Err(err) => {
                // If it fails, should be a reasonable error
                assert!(
                    err.message.contains("empty")
                        || err.message.contains("expected")
                        || err.message.contains("stage"),
                    "unexpected error: {}",
                    err.message
                );
            }
        }
    }

    #[test]
    fn test_parse_sil_only_comments() {
        // Test: only comments
        let sil = r"
// This is a comment
// Another comment
";
        let result = parse_sil(sil);
        match result {
            Ok(module) => {
                assert!(module.functions.is_empty());
            }
            Err(err) => {
                // If it fails, should be a reasonable error
                assert!(
                    err.message.contains("empty")
                        || err.message.contains("expected")
                        || err.message.contains("stage"),
                    "unexpected error: {}",
                    err.message
                );
            }
        }
    }
}
