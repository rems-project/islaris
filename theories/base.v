From Coq Require Export ssreflect.
From stdpp Require Export prelude strings gmap.
From RecordUpdate Require Export RecordSet.
From refframe Require Export module.
Export RecordSetNotations.

Open Scope Z_scope.

Global Set Default Proof Using "Type".
Global Unset Program Cases.
Global Set Keyed Unification.
Global Set Default Goal Selector "!".

Lemma TraceStep' {EV} κs κs' (m : module EV) σ2 σ1 σ3 κ :
  m.(m_step) σ1 κ σ2 →
  κs = option_list (Vis <$> κ) ++ κs' →
  σ2 ~{ m, κs' }~> σ3 →
  σ1 ~{ m, κs }~> σ3.
Proof. move => ? -> ?. by apply: TraceStep. Qed.
