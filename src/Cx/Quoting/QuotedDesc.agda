
module Cx.Quoting.QuotedDesc where

open import Common
open import Reflection

open import Cx.Named

record QuotedDesc : Set₂ where
  constructor mk
  field
    {I} : Cx
    {Γ} : Cx
    {#c} : Nat
    `datatypeName : Name
    `constructorNames : Vec Name #c
    desc : DatDesc I Γ #c
