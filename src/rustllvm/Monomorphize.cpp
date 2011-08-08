#include "llvm/Type.h"
#include <llvm-c/Core.h>
#include <cassert>

using namespace llvm;


// Type folds

namespace {

template<typename T,typename U>
class TypeFold {
public:
    U Fold(Type *Ty) const;
};

}

template<typename T,typename U>
U TypeFold::Fold(Type *Ty) const {
  PointerType *PTy;
  ArrayType *ATy;
  VectorType *VTy;

  switch (Ty->getTypeID()) {
  case Type::VoidTyID:
  case Type::FloatTyID:
  case Type::DoubleTyID:
  case Type::X86_FP80TyID:
  case Type::FP128TyID:
  case Type::PPC_FP128TyID:
  case Type::LabelTyID:
  case Type::MetadataTyID:
  case Type::X86_MMXTyID:
  case Type::IntegerTyID:
    return static_cast<T *>(this)->FoldSimpleType(Ty);
  case Type::FunctionTyID:
    return static_cast<T *>(this)->FoldFunctionType(cast<FunctionType>(Ty));
  case Type::StructTyID:
    return static_cast<T *>(this)->FoldStructType(cast<StructType>(Ty));
  case Type::PointerTyID:
    PTy = cast<PointerType>(Ty);
    return static_cast<T *>(this)->FoldPointerType(cast<PointerType>(Ty));
    return PointerType::get(Monomorphize(PTy->getElementType()),
                            PTy->getAddressSpace());
  case Type::ArrayTyID:
    return static_cast<T *>(this)->FoldArrayType(cast<ArrayType>(Ty));
    ATy = cast<ArrayType>(Ty);
    return ArrayType::get(Monomorphize(ATy->getElementType()),
                          ATy->getNumElements());
  case Type::VectorTyID:
    return static_cast<T *>(this)->FoldVectorType(cast<VectorType>(Ty));
    VTy = cast<VectorType>(Ty);
    return VectorType::get(Monomorphize(VTy->getElementType()),
                           VTy->getNumElements());
  default:
    assert(0 && "Unrecognized type!");
  }
}


// Type monomorphization

namespace {

class TypeMonomorphizer : public TypeFold<TypeMonomorphizer,Type *> {
private:
    Type **ReplacementTypes;
    unsigned ReplacementTypeCount;

    Type *MonomorphizeAnonymousStructType(StructType *STy) const;

public:
    TypeMonomorphizer(Type **RT, unsigned RTCount)
    : ReplacementTypes(RT), ReplacementTypeCount(RTCount) {}

    Type *FoldSimpleType(Type *Ty) const { return Ty; }
    Type *FoldFunctionType(FunctionType *FTy) const;
    Type *FoldStructType(StructType *STy) const;
    Type *FoldPointerType(PointerType *PTy) const;

    Type *Monomorphize(Type *Ty) const;
};

} // end anonymous namespace

FunctionType *TypeMonomorphizer::MonomorphizeFunctionType(FunctionType *FTy)
    const {
  Type *ReturnType = Monomorphize(FTy->getReturnType());

  Type *Params[FTy->getNumParams()];
  for (unsigned i = 0; i < FTy->getNumParams(); i++)
    Params[i] = Monomorphize(FTy->getParamType(i));
  ArrayRef<Type *> ParamsArray(Params, FTy->getNumParams());

  return FunctionType::get(ReturnType, ParamsArray, FTy->isVarArg());
}

StructType *TypeMonomorphizer::MonomorphizeAnonymousStructType(StructType *STy)
    const {
  Type *Elements[STy->getNumElements()];
  for (unsigned i = 0; i < STy->getNumElements(); i++)
    Elements[i] = Monomorphize(STy->getElementType(i));
  ArrayRef<Type *> ElementsArray(Elements, STy->getNumElements());
  return StructType::get(STy->getContext(), ElementsArray, STy->isPacked());
}

Type *TypeMonomorphizer::MonomorphizeStructType(StructType *STy) const {
  if (STy->isAnonymous())
    return MonomorphizeAnonymousStructType(STy);

  if (STy->getName().startswith("typaram_")) {
    assert(STy->getName().size() + 1 >= sizeof("typaram_0") &&
           "\"typaram_\" is not a legal struct name!");
    StringRef NumericPart = (STy->getName().data() + sizeof("typaram_") - 1);
    unsigned ParamIndex;
    assert(!NumericPart.getAsInteger(10, ParamIndex) &&
           "\"typaram_\" must be followed by a number!");
    assert(ParamIndex < ReplacementTypeCount &&
           "Param index out of range!");
    return ReplacementTypes[ParamIndex];
  }

  return STy; // Numeric struct type. We assume we never monomorphize these.
}


extern "C" LLVMTypeRef LLVMRustReplaceTypes(LLVMTypeRef Ty,
    LLVMTypeRef *ReplacementTypes, unsigned ReplacementTypeCount) {
  TypeMonomorphizer TMM(reinterpret_cast<Type **>(ReplacementTypes),
                        ReplacementTypeCount);
  return reinterpret_cast<LLVMTypeRef>(TMM.Monomorphize(unwrap(Ty)));
}


// Performs substitution on function bodies to monomorphize them.

extern "C" LLVMValueRef LLVMRustMonomorphizeFunction(LLVMValueRef Function,
    LLVMTypeRef *Types, unsigned TypeCount) {
  Function *F = cast<Function>(reinterpret_cast<Value *>(Function));
  
}


