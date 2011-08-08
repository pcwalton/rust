#include "llvm/Type.h"
#include <llvm-c/Core.h>

using namespace llvm;

namespace {

class TypeMonomorphizer {
private:
  Type **ReplacementTypes;
  unsigned ReplacementTypeCount;

public:
  TypeMonomorphizer(Type **RT, unsigned RTCount)
  : ReplacementTypes(RT), ReplacementTypeCount(RTCount) {}

  Type *Monomorphize(Type *Ty) const;
};

} // end anonymous namespace

// Monomorphizes a type by replacing type placeholders with their
// substitutions.
Type *TypeMonomorphizer::Monomorphize(Type *Ty) const {
  return Ty;  // TODO
}

extern "C" LLVMTypeRef LLVMRustReplaceTypes(LLVMTypeRef Ty,
    LLVMTypeRef *ReplacementTypes, unsigned ReplacementTypeCount) {
  TypeMonomorphizer TMM(reinterpret_cast<Type **>(ReplacementTypes),
                        ReplacementTypeCount);
  return wrap(TMM.Monomorphize(unwrap(Ty)));
}

