import Lake
open Lake DSL System

require velvet from ".." / "velvet"
require LemmaScript from ".." / "LemmaScript"

package ColorWheelLemmaScript where
  leanOptions := #[⟨`pp.unicode.fun, true⟩]

@[default_target]
lean_lib ColorWheel where
  srcDir := "src"
  roots := #[`«colorwheel.types», `«colorwheel.spec», `«colorwheel.def», `«colorwheel.proof», `«colorwheel.props»]
