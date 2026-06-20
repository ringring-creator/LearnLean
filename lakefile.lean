import Lake
open Lake DSL

package "LearnLean" where
  version := v!"0.1.0"

@[default_target]
lean_lib «LearnLean» where
  -- add library configuration options here
