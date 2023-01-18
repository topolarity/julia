// This file is a part of Julia. License is MIT: https://julialang.org/license

#ifndef JL_CODEGEN_H
#define JL_CODEGEN_H

// TODO: Update Makefile with dependencies

#include "julia.h"
#include "jitlayers.h"
#include <llvm/IR/Metadata.h>
#include <llvm/IR/Instruction.h>

enum AddressSpace {
    Generic = 0,
    Tracked = 10,
    Derived = 11,
    CalleeRooted = 12,
    Loaded = 13,
    FirstSpecial = Tracked,
    LastSpecial = Loaded,
};

namespace JuliaType {
    static inline llvm::StructType* get_jlvalue_ty(llvm::LLVMContext &C) {
        return llvm::StructType::get(C);
    }

    static inline llvm::PointerType* get_pjlvalue_ty(llvm::LLVMContext &C, unsigned addressSpace=0) {
        return llvm::PointerType::get(get_jlvalue_ty(C), addressSpace);
    }

    static inline llvm::PointerType* get_prjlvalue_ty(llvm::LLVMContext &C) {
        return llvm::PointerType::get(get_jlvalue_ty(C), AddressSpace::Tracked);
    }

    static inline llvm::PointerType* get_ppjlvalue_ty(llvm::LLVMContext &C) {
        return llvm::PointerType::get(get_pjlvalue_ty(C), 0);
    }

    static inline llvm::PointerType* get_pprjlvalue_ty(llvm::LLVMContext &C) {
        return llvm::PointerType::get(get_prjlvalue_ty(C), 0);
    }

    static inline auto get_jlfunc_ty(llvm::LLVMContext &C) {
        auto T_prjlvalue = get_prjlvalue_ty(C);
        auto T_pprjlvalue = llvm::PointerType::get(T_prjlvalue, 0);
        return llvm::FunctionType::get(T_prjlvalue, {
                T_prjlvalue,  // function
                T_pprjlvalue, // args[]
                llvm::Type::getInt32Ty(C)}, // nargs
            false);
    }

    static inline auto get_jlfunc2_ty(llvm::LLVMContext &C) {
        auto T_prjlvalue = get_prjlvalue_ty(C);
        auto T_pprjlvalue = llvm::PointerType::get(T_prjlvalue, 0);
        return llvm::FunctionType::get(T_prjlvalue, {
                T_prjlvalue,  // function
                T_pprjlvalue, // args[]
                llvm::Type::getInt32Ty(C),
                T_prjlvalue,  // linfo
                }, // nargs
            false);
    }

    static inline auto get_jlfuncparams_ty(llvm::LLVMContext &C) {
        auto T_prjlvalue = get_prjlvalue_ty(C);
        auto T_pprjlvalue = llvm::PointerType::get(T_prjlvalue, 0);
        return llvm::FunctionType::get(T_prjlvalue, {
                T_prjlvalue,  // function
                T_pprjlvalue, // args[]
                llvm::Type::getInt32Ty(C),
                T_pprjlvalue,  // linfo->sparam_vals
                }, // nargs
            false);
    }

    static inline auto get_voidfunc_ty(llvm::LLVMContext &C) {
        return llvm::FunctionType::get(llvm::Type::getVoidTy(C), /*isVarArg*/false);
    }

    static inline auto get_pvoidfunc_ty(llvm::LLVMContext &C) {
        return get_voidfunc_ty(C)->getPointerTo();
    }
}

class jl_codectx_t;

// types
struct jl_typecache_t {
    Type *T_jlvalue;
    Type *T_pjlvalue;
    Type *T_prjlvalue;
    Type *T_ppjlvalue;
    Type *T_pprjlvalue;
    StructType *T_jlarray;
    Type *T_pjlarray;
    FunctionType *T_jlfunc;
    FunctionType *T_jlfuncparams;

    IntegerType *T_sigatomic;

    Type *T_ppint8;

    bool initialized;

    jl_typecache_t() :
        T_jlvalue(nullptr), T_pjlvalue(nullptr), T_prjlvalue(nullptr),
        T_ppjlvalue(nullptr), T_pprjlvalue(nullptr), T_jlarray(nullptr),
        T_pjlarray(nullptr), T_jlfunc(nullptr), T_jlfuncparams(nullptr),
        T_sigatomic(nullptr), T_ppint8(nullptr), initialized(false) {}

    void initialize(LLVMContext &context);
};

struct jl_tbaacache_t {
    // type-based alias analysis nodes.  Indentation of comments indicates hierarchy.
    MDNode *tbaa_root;     // Everything
    MDNode *tbaa_gcframe;    // GC frame
    // LLVM should have enough info for alias analysis of non-gcframe stack slot
    // this is mainly a place holder for `jl_cgval_t::tbaa`
    MDNode *tbaa_stack;      // stack slot
    MDNode *tbaa_unionselbyte;   // a selector byte in isbits Union struct fields
    MDNode *tbaa_data;       // Any user data that `pointerset/ref` are allowed to alias
    MDNode *tbaa_binding;        // jl_binding_t::value
    MDNode *tbaa_value;          // jl_value_t, that is not jl_array_t
    MDNode *tbaa_mutab;              // mutable type
    MDNode *tbaa_datatype;               // datatype
    MDNode *tbaa_immut;              // immutable type
    MDNode *tbaa_ptrarraybuf;    // Data in an array of boxed values
    MDNode *tbaa_arraybuf;       // Data in an array of POD
    MDNode *tbaa_array;      // jl_array_t
    MDNode *tbaa_arrayptr;       // The pointer inside a jl_array_t
    MDNode *tbaa_arraysize;      // A size in a jl_array_t
    MDNode *tbaa_arraylen;       // The len in a jl_array_t
    MDNode *tbaa_arrayflags;     // The flags in a jl_array_t
    MDNode *tbaa_arrayoffset;     // The offset in a jl_array_t
    MDNode *tbaa_arrayselbyte;   // a selector byte in a isbits Union jl_array_t
    MDNode *tbaa_const;      // Memory that is immutable by the time LLVM can see it
    bool initialized;

    jl_tbaacache_t(): tbaa_root(nullptr), tbaa_gcframe(nullptr), tbaa_stack(nullptr),
                    tbaa_unionselbyte(nullptr), tbaa_data(nullptr), tbaa_binding(nullptr),
                    tbaa_value(nullptr), tbaa_mutab(nullptr), tbaa_datatype(nullptr),
                    tbaa_immut(nullptr), tbaa_ptrarraybuf(nullptr), tbaa_arraybuf(nullptr),
                    tbaa_array(nullptr), tbaa_arrayptr(nullptr), tbaa_arraysize(nullptr),
                    tbaa_arraylen(nullptr), tbaa_arrayflags(nullptr), tbaa_arrayoffset(nullptr),
                    tbaa_arrayselbyte(nullptr), tbaa_const(nullptr), initialized(false) {}

    auto tbaa_make_child(MDBuilder &mbuilder, const char *name, MDNode *parent = nullptr, bool isConstant = false) {
        MDNode *scalar = mbuilder.createTBAAScalarTypeNode(name, parent ? parent : tbaa_root);
        MDNode *n = mbuilder.createTBAAStructTagNode(scalar, scalar, 0, isConstant);
        return std::make_pair(n, scalar);
    }

    void initialize(llvm::LLVMContext &context);
};

struct jl_noaliascache_t {
    // Each domain operates completely independently.
    // "No aliasing" is inferred if it is implied by any domain.

    // memory regions domain
    struct jl_regions_t {
        MDNode *gcframe;        // GC frame
        MDNode *stack;          // Stack slot
        MDNode *data;           // Any user data that `pointerset/ref` are allowed to alias
        MDNode *type_metadata;  // Non-user-accessible type metadata incl. size, union selectors, etc.
        MDNode *constant;       // Memory that is immutable by the time LLVM can see it

        jl_regions_t(): gcframe(nullptr), stack(nullptr), data(nullptr), type_metadata(nullptr), constant(nullptr) {}

        void initialize(llvm::LLVMContext &context);
    } regions;

    // `@aliasscope` domain
    struct jl_aliasscope_t {
        MDNode *current;

        jl_aliasscope_t(): current(nullptr) {}

        // No init required, this->current is only used to store the currently active aliasscope
        void initialize(llvm::LLVMContext &context) {}
    } aliasscope;

    bool initialized;

    jl_noaliascache_t(): regions(), aliasscope(), initialized(false) {}

    void initialize(llvm::LLVMContext &context);
};

struct jl_debugcache_t {
    // Basic DITypes
    DIDerivedType *jl_pvalue_dillvmt;
    DIDerivedType *jl_ppvalue_dillvmt;
    DISubroutineType *jl_di_func_sig;
    DISubroutineType *jl_di_func_null_sig;
    bool initialized;

    jl_debugcache_t()
    : jl_pvalue_dillvmt(nullptr), jl_ppvalue_dillvmt(nullptr),
    jl_di_func_sig(nullptr), jl_di_func_null_sig(nullptr), initialized(false) {}

    void initialize(Module *m);
};

// Alias Analysis Info (analogous to llvm::AAMDNodes)
struct jl_aliasinfo_t {
    using MDNode = llvm::MDNode;
    using Instruction = llvm::Instruction;

    MDNode *tbaa = nullptr;          // '!tbaa': Struct-path TBAA. TBAA graph forms a tree (indexed by offset).
                                     //          Two pointers do not alias if they are not transitive parents
                                     //          (effectively, subfields) of each other or equal.
    MDNode *tbaa_struct = nullptr;   // '!tbaa.struct': Describes memory layout of struct.
    MDNode *scope = nullptr;         // '!alias.scope': Generic "noalias" memory access sets.
                                     //                 If alias.scope(inst_a) ⊆ noalias(inst_b) (in any "domain")
                                     //                    => inst_a, inst_b do not alias.
    MDNode *noalias = nullptr;       // '!noalias': See '!alias.scope' above.

    enum class Region { unknown, gcframe, stack, data, constant, type_metadata }; // See jl_regions_t

    explicit jl_aliasinfo_t() = default;
    explicit jl_aliasinfo_t(jl_codectx_t &ctx, Region r, MDNode *tbaa);
    explicit jl_aliasinfo_t(MDNode *tbaa, MDNode *tbaa_struct, MDNode *scope, MDNode *noalias)
        : tbaa(tbaa), tbaa_struct(tbaa_struct), scope(scope), noalias(noalias) {}
    jl_aliasinfo_t(const jl_aliasinfo_t &) = default;

       //bool operator==(const AAMDNodes &A) const {
     //return TBAA == A.TBAA && TBAAStruct == A.TBAAStruct && Scope == A.Scope &&
            //NoAlias == A.NoAlias;
   //}

   //bool operator!=(const AAMDNodes &A) const { return !(*this == A); }

    explicit operator bool() const {
        return this->tbaa || this->tbaa_struct || this->scope || this->noalias;
    }

    // Add !tbaa, !tbaa.struct, !alias.scope, !noalias annotations to an instruction.
    //
    // Also adds `invariant.load` to load instructions in the constant !noalias scope.
    Instruction *decorateInst(Instruction *inst) const;

    // Merge two sets of alias information.
    jl_aliasinfo_t merge(const jl_aliasinfo_t &other) const;

    // TODO: Test this still matches, then delete

    // Create alias information based on the provided TBAA metadata.
    //
    // This function only exists to help transition to using !noalias to encode
    // memory region non-aliasing. It should be deleted once the TBAA metadata
    // is improved to encode only memory layout and *not* memory regions.
    static jl_aliasinfo_t fromTBAA(jl_codectx_t &ctx, MDNode *tbaa);
};

using Region = jl_aliasinfo_t::Region;

// metadata tracking for a llvm Value* during codegen
struct jl_cgval_t {
    Value *V; // may be of type T* or T, or set to NULL if ghost (or if the value has not been initialized yet, for a variable definition)
    // For unions, we may need to keep a reference to the boxed part individually.
    // If this is non-NULL, then, at runtime, we satisfy the invariant that (for the corresponding
    // runtime values) if `(TIndex | 0x80) != 0`, then `Vboxed == V` (by value).
    // For convenience, we also set this value of isboxed values, in which case
    // it is equal (at compile time) to V.
    // If this is non-NULL, it is always of type `T_prjlvalue`
    Value *Vboxed;
    Value *TIndex; // if `V` is an unboxed (tagged) Union described by `typ`, this gives the DataType index (1-based, small int) as an i8
    jl_value_t *constant; // constant value (rooted in linfo.def.roots)
    jl_value_t *typ; // the original type of V, never NULL
    bool isboxed; // whether this value is a jl_value_t* allocated on the heap with the right type tag
    bool isghost; // whether this value is "ghost"
    // The related alias information (!tbaa, !tbaa.struct, !noalias, and !alias.scope)
    // This jl_cgval_t holds an address (i.e. is a pointer) iff aliasinfo is all NULL
    jl_aliasinfo_t aliasinfo;
    // If non-null, this memory location may be promoted on use, by hoisting the
    // destination memory above the promotion point.
    Instruction *promotion_point;
    // If promotion_ssa is non-null, the julia src ssa value that corresponds
    // to the promotion point. This is used for dominator analysis, since LLVM's
    // dominator analysis has algorithmic problems for large basic blocks.
    ssize_t promotion_ssa;
    bool ispointer() const
    {
        // whether this value is compatible with `data_pointer`
        return bool(aliasinfo);
    }

    jl_cgval_t(Value *Vval, jl_value_t *typ, Value *tindex) : // general value constructor
        V(Vval), // V is allowed to be NULL in a jl_varinfo_t context, but not during codegen contexts
        Vboxed(nullptr),
        TIndex(tindex),
        constant(NULL),
        typ(typ),
        isboxed(false),
        isghost(false),
        aliasinfo(),
        promotion_point(nullptr),
        promotion_ssa(-1)
    {
        assert(TIndex == NULL || TIndex->getType() == llvm::ArrayType::getInt8Ty(TIndex->getContext()));
    }

    jl_cgval_t(Value *Vptr, bool isboxed, jl_value_t *typ, Value *tindex, jl_aliasinfo_t aliasinfo) : // general pointer constructor
        V(Vptr),
        Vboxed(isboxed ? Vptr : nullptr),
        TIndex(tindex),
        constant(NULL),
        typ(typ),
        isboxed(isboxed),
        isghost(false),
        aliasinfo(aliasinfo),
        promotion_point(nullptr),
        promotion_ssa(-1)
    {
        if (Vboxed)
            assert(Vboxed->getType() == JuliaType::get_prjlvalue_ty(Vboxed->getContext()));
        assert(aliasinfo); // TODO: unclear?
        assert(!(isboxed && TIndex != NULL));
        assert(TIndex == NULL || TIndex->getType() == llvm::ArrayType::getInt8Ty(TIndex->getContext()));
    }

    explicit jl_cgval_t(jl_value_t *typ) : // ghost value constructor
        // mark explicit to avoid being used implicitly for conversion from NULL (use jl_cgval_t() instead)
        V(NULL),
        Vboxed(NULL),
        TIndex(NULL),
        constant(((jl_datatype_t*)typ)->instance),
        typ(typ),
        isboxed(false),
        isghost(true),
        aliasinfo(),
        promotion_point(nullptr),
        promotion_ssa(-1)
    {
        assert(jl_is_datatype(typ));
        assert(constant);
    }

    jl_cgval_t(const jl_cgval_t &v, jl_value_t *typ, Value *tindex); // copy constructor with new type

    explicit jl_cgval_t() : // undef / unreachable constructor
        V(NULL),
        Vboxed(NULL),
        TIndex(NULL),
        constant(NULL),
        typ(jl_bottom_type),
        isboxed(false),
        isghost(true),
        aliasinfo(),
        promotion_point(nullptr),
        promotion_ssa(-1)
    {
    }
};

// per-local-variable information
struct jl_varinfo_t {
    Instruction *boxroot; // an address, if the var might be in a jl_value_t** stack slot (marked ctx.tbaa().tbaa_const, if appropriate)
    jl_cgval_t value; // a stack slot or constant value
    Value *pTIndex; // i8* stack slot for the value.TIndex tag describing `value.V`
    DILocalVariable *dinfo;
    // if the variable might be used undefined and is not boxed
    // this i1 flag is true when it is defined
    Value *defFlag;
    bool isSA; // whether all stores dominate all uses
    bool isVolatile;
    bool isArgument;
    bool usedUndef;
    bool used;

    jl_varinfo_t(LLVMContext &ctxt) : boxroot(NULL),
                     value(jl_cgval_t()),
                     pTIndex(NULL),
                     dinfo(NULL),
                     defFlag(NULL),
                     isSA(false),
                     isVolatile(false),
                     isArgument(false),
                     usedUndef(false),
                     used(false)
    {
    }
};

// information about the context of a piece of code: its enclosing
// function and module, and visible local variables and labels.
class jl_codectx_t {
public:
    IRBuilder<> builder;
    jl_codegen_params_t &emission_context;
    llvm::MapVector<jl_code_instance_t*, jl_codegen_call_target_t> call_targets;
    std::map<void*, GlobalVariable*> &global_targets;
    std::map<std::tuple<jl_code_instance_t*, bool>, Function*> &external_calls;
    Function *f = NULL;
    // local var info. globals are not in here.
    std::vector<jl_varinfo_t> slots;
    std::map<int, jl_varinfo_t> phic_slots;
    std::vector<jl_cgval_t> SAvalues;
    std::vector<std::tuple<jl_cgval_t, BasicBlock *, AllocaInst *, PHINode *, jl_value_t *>> PhiNodes;
    std::vector<bool> ssavalue_assigned;
    std::vector<int> ssavalue_usecount;
    std::vector<orc::ThreadSafeModule> oc_modules;
    jl_module_t *module = NULL;
    jl_typecache_t type_cache;
    jl_tbaacache_t tbaa_cache;
    jl_noaliascache_t aliasscope_cache;
    jl_method_instance_t *linfo = NULL;
    jl_value_t *rettype = NULL;
    jl_code_info_t *source = NULL;
    jl_array_t *code = NULL;
    size_t world = 0;
    const char *name = NULL;
    StringRef file{};
    ssize_t *line = NULL;
    Value *spvals_ptr = NULL;
    Value *argArray = NULL;
    Value *argCount = NULL;
    std::string funcName;
    int vaSlot = -1;        // name of vararg argument
    int nReqArgs = 0;
    int nargs = 0;
    int nvargs = -1;
    bool is_opaque_closure = false;

    Value *pgcstack = NULL;
    Instruction *topalloca = NULL;

    bool debug_enabled = false;
    bool use_cache = false;
    bool external_linkage = false;
    const jl_cgparams_t *params = NULL;

    std::vector<std::unique_ptr<Module>> llvmcall_modules;

    jl_codectx_t(LLVMContext &llvmctx, jl_codegen_params_t &params);
    jl_typecache_t &types();
    jl_tbaacache_t &tbaa();
    jl_noaliascache_t &noalias();
    ~jl_codectx_t();
};

#endif
