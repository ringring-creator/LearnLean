import Lake
open Lake DSL

package "LearnLean" where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
  
@[default_target]
lean_lib «LearnLean» where
  globs := #[.submodules `LearnLean]
