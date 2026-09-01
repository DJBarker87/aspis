import V7Tag73CurrentHelpersOpaque.CircleTableSupport

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
noncomputable section

namespace V7Tag73CurrentHelpersOpaque
namespace staged_circle_tables

def RATE512_CIRCLE_HIGH9_WINDOW_chunk00 : Array (Array Std.U32 2#usize) 16#usize :=
  ⟨[
    circle_pair 1#u32 0#u32,
    circle_pair 1434706457#u32 1835793811#u32,
    circle_pair 13610297#u32 1064696601#u32,
    circle_pair 609228044#u32 827893883#u32,
    circle_pair 785043271#u32 1260750973#u32,
    circle_pair 477465227#u32 1464821634#u32,
    circle_pair 655387905#u32 752064346#u32,
    circle_pair 1919800332#u32 1732277387#u32,
    circle_pair 838195206#u32 1774253895#u32,
    circle_pair 904293309#u32 989947986#u32,
    circle_pair 951582730#u32 528066207#u32,
    circle_pair 941653828#u32 2075806777#u32,
    circle_pair 1357626641#u32 2066105389#u32,
    circle_pair 88230288#u32 1857622143#u32,
    circle_pair 810533124#u32 839591040#u32,
    circle_pair 767685501#u32 566492308#u32
  ], by rfl⟩

end staged_circle_tables
end V7Tag73CurrentHelpersOpaque
