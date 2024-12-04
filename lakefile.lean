import Lake
open Lake DSL

package «Zeta3Irrational» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩
  ]
  -- add any additional package configuration options here

@[default_target]
lean_lib «Zeta3Irrational» where
  -- add any library configuration options here

require checkdecls from git "https://github.com/PatrickMassot/checkdecls.git"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "e348a4c"

require «PrimeNumberTheoremAnd» from git
  "https://github.com/AlexKontorovich/PrimeNumberTheoremAnd.git" @ "main"

-- meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "b6ae1cf"
