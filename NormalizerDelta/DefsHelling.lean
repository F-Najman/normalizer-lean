module

public import NormalizerLean.Defs

@[expose] public section

/-! Part 9 needs no new definitions: it uses `Gamma0Plus`, `SL2ZR`, `NormG`, `BG` and `projSL` of
`NormalizerLean/Defs.lean`.  This file only imports them, so that `StatementsHelling.lean`, which imports this file,
is unchanged after freezing. -/
