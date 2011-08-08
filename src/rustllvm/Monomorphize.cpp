#include "llvm/Type.h"
#include <llvm-c/Core.h>
#include <cassert>

using namespace llvm;

namespace {

class TypeMonomorphizer {
private:
  Type **ReplacementTypes;
  unsigned ReplacementTypeCount;

  FunctionType *MonomorphizeFunctionType(FunctionType *FTy) const;
  Type *MonomorphizeStructType(StructType *STy) const;
  StructType *MonomorphizeAnonymousStructType(StructType *STy) const;

public:
  TypeMonomorphizer(Type **RT, unsigned RTCount)
  : ReplacementTypes(RT), ReplacementTypeCount(RTCount) {}

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

// Monomorphizes a type by replacing type placeholders with their
// substitutions.
Type *TypeMonomorphizer::Monomorphize(Type *Ty) const {
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
    return Ty;
  case Type::FunctionTyID:
    return MonomorphizeFunctionType(cast<FunctionType>(Ty));
  case Type::StructTyID:
    return MonomorphizeStructType(cast<StructType>(Ty));
  case Type::PointerTyID:
    PTy = cast<PointerType>(Ty);
    return PointerType::get(Monomorphize(PTy->getElementType()),
                            PTy->getAddressSpace());
  case Type::ArrayTyID:
    ATy = cast<ArrayType>(Ty);
    return ArrayType::get(Monomorphize(ATy->getElementType()),
                          ATy->getNumElements());
  case Type::VectorTyID:
    VTy = cast<VectorType>(Ty);
    return VectorType::get(Monomorphize(VTy->getElementType()),
                           VTy->getNumElements());
  default:
    assert(0 && "Unrecognized type!");
  }
  return Ty;  // TODO
}

extern "C" LLVMTypeRef LLVMRustReplaceTypes(LLVMTypeRef Ty,
    LLVMTypeRef *ReplacementTypes, unsigned ReplacementTypeCount) {
  TypeMonomorphizer TMM(reinterpret_cast<Type **>(ReplacementTypes),
                        ReplacementTypeCount);
  return reinterpret_cast<LLVMTypeRef>(TMM.Monomorphize(unwrap(Ty)));
}

