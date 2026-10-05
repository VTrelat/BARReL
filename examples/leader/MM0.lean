import examples.leader.Tree

set_option barrel.atelierb "/Applications/atelierb-free-arm64-24.04.2.app/Contents/Resources"

open B.Builtins

import system mm0 from "specs/leader"

next obligation by
  introv
  intro _ _ _ _ _ _ hroot_spec _ _ _ hroot hparent hrooted
  obtain ⟨htotal, -, hconnected⟩ := (hroot_spec nn fi hroot hparent).mp hrooted
  exact Leader.rooted_tree_asymmetric htotal hroot hconnected

qed mm0
