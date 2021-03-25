From Coq Require Export ssreflect.
From stdpp Require Export prelude strings gmap.
From RecordUpdate Require Export RecordSet.
From refframe Require Export module.
From refinedc.lang Require Export base.
Export RecordSetNotations.

Open Scope Z_scope.

Global Set Default Proof Using "Type".
Global Unset Program Cases.
Global Set Keyed Unification.
Global Set Default Goal Selector "!".

Arguments set _ _ _ _ _ !_ /.
