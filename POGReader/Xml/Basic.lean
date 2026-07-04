/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Dany Fabian

Vendored from Lean core `Lean.Data.Xml.Basic` (leanprover/lean4 @ v4.28.0), which was
removed from core in v4.29.0 (PR #12302: "chore: remove unused `Lean.Data.Xml`"). Kept
here so BARReL can build on Lean ≥ v4.29.0. Only change vs upstream: dropped the module-
system boilerplate (`module`/`prelude`/`public`) and re-namespaced `Lean.Xml` → `B.Xml`.
-/
import Std.Data.TreeMap.Basic
import Init.Data.Ord.String

namespace B
namespace Xml

abbrev Attributes := Std.TreeMap String String
instance : ToString Attributes := ⟨λ as => as.foldl (λ s n v => s ++ s!" {n}=\"{v}\"") ""⟩

mutual
inductive Element
| Element
  (name : String)
  (attributes : Attributes)
  (content : Array Content)

inductive Content
| Element (element : Element)
| Comment (comment : String)
| Character (content : String)
deriving Inhabited
end

mutual
private partial def eToString : Element → String
| Element.Element n a c => s!"<{n}{a}>{c.map cToString |>.foldl (· ++ ·) ""}</{n}>"

private partial def cToString : Content → String
| Content.Element e => eToString e
| Content.Comment c => s!"<!--{c}-->"
| Content.Character c => c

end
instance : ToString Element := ⟨eToString⟩
instance : ToString Content := ⟨cToString⟩

end Xml
end B
