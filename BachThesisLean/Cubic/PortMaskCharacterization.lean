import BachThesisLean.Cubic.PortMasks
import BachThesisLean.Cubic.MatchingCovered

namespace BachThesisLean
namespace BipartiteMultigraph

universe u v w

variable {X : Type u} {Y : Type v} {E : Type w}
variable [Fintype X] [Fintype Y] [Fintype E]
variable [DecidableEq X] [DecidableEq Y] [DecidableEq E]

/-!
# Global port-mask characterization

The local mask theorem already handles nonincident edge pairs.  For incident
pairs one uses a third edge at their common cubic root and extends that edge to
a perfect matching.  `MatchingCovered.lean` now proves this extension directly
from cubic bipartite regularity, so the manuscript's connected cubic statement
is available without an extra matching-covered hypothesis.
-/

/-- Under cubicity and matching-coveredness, the manuscript's mask condition
is sufficient for EEP. -/
theorem hasEEP_of_edgeRootMask_card_ge_two_of_matchingCovered
    (G : BipartiteMultigraph X Y E) (hG : G.IsCubic)
    (hMC : G.IsMatchingCovered)
    (hmask : ∀ (r : X ⊕ Y) (e : E), ¬ G.Incident e r →
      2 ≤ (G.edgeRootMask r (G.portsOfCubic hG r) e).card) :
    G.HasEEP := by
  classical
  intro e f hef
  let r : X ⊕ Y := .inl (G.left f)
  have hfr : G.Incident f r := by
    simp [r, Incident]
  by_cases her : G.Incident e r
  · let ports : G.PortEnumeration r := G.portsOfCubic hG r
    let er : {g : E // g ∈ G.incidentEdges r} :=
      ⟨e, (mem_incidentEdges G r e).2 her⟩
    let fr : {g : E // g ∈ G.incidentEdges r} :=
      ⟨f, (mem_incidentEdges G r f).2 hfr⟩
    let ie : Fin 3 := ports.symm er
    let iF : Fin 3 := ports.symm fr
    have hief : ie ≠ iF := by
      intro hidx
      have hsub : er = fr := by
        apply ports.symm.injective
        simpa [ie, iF] using hidx
      exact hef (congrArg Subtype.val hsub)
    have hnotSubset :
        ¬ (Finset.univ : Finset (Fin 3)) ⊆ ({ie, iF} : Finset (Fin 3)) := by
      intro hsub
      have hcard := Finset.card_le_card hsub
      simp [hief] at hcard
    obtain ⟨k, _hkUniv, hkpair⟩ := Finset.not_subset.mp hnotSubset
    have hk : k ≠ ie ∧ k ≠ iF := by
      simpa using hkpair
    let g : E := (ports k).val
    obtain ⟨P, hP, hgP⟩ := hMC.2.2 g
    have hiePort : (ports ie).val = e := by
      have hp : ports ie = er := by
        simpa [ie] using ports.apply_symm_apply er
      exact congrArg Subtype.val hp
    have hiFPort : (ports iF).val = f := by
      have hp : ports iF = fr := by
        simpa [iF] using ports.apply_symm_apply fr
      exact congrArg Subtype.val hp
    obtain ⟨m, hmP, hmUnique⟩ := hP.existsUnique_port r ports
    have hkm : k = m := by
      apply hmUnique k
      simpa [g] using hgP
    have heNotP : e ∉ P := by
      intro heP
      have hieP : (ports ie).val ∈ P := by
        rw [hiePort]
        exact heP
      have hiem : ie = m := hmUnique ie hieP
      exact hk.1 (hkm.trans hiem.symm)
    have hfNotP : f ∉ P := by
      intro hfP
      have hiFP : (ports iF).val ∈ P := by
        rw [hiFPort]
        exact hfP
      have hiFm : iF = m := hmUnique iF hiFP
      exact hk.2 (hkm.trans hiFm.symm)
    have heCompl : e ∈ Pᶜ := Finset.mem_compl.mpr heNotP
    have hfCompl : f ∈ Pᶜ := Finset.mem_compl.mpr hfNotP
    exact ⟨P, r, hP,
      G.componentCarries_of_mem_of_incident heCompl her,
      G.componentCarries_of_mem_of_incident hfCompl hfr⟩
  · let ports : G.PortEnumeration r := G.portsOfCubic hG r
    let fr : {g : E // g ∈ G.incidentEdges r} :=
      ⟨f, (mem_incidentEdges G r f).2 hfr⟩
    let iF : Fin 3 := ports.symm fr
    have hiFPort : (ports iF).val = f := by
      have hp : ports iF = fr := by
        simpa [iF] using ports.apply_symm_apply fr
      exact congrArg Subtype.val hp
    have hcard : 2 ≤ (G.edgeRootMask r ports e).card := by
      simpa [ports] using hmask r e her
    have hlt : 1 < (G.edgeRootMask r ports e).card := by omega
    obtain ⟨j, hj, hji⟩ :=
      Finset.exists_mem_ne hlt iF
    have hw : G.EdgePairWitness e (ports iF).val :=
      (G.edgePairWitness_port_iff_exists_mask_ne r ports e iF).2
        ⟨j, hj, hji⟩
    rw [hiFPort] at hw
    exact hw

/-- The boxed port-mask characterization of EEP with matching-coveredness made
explicit as a reusable intermediate theorem. -/
theorem hasEEP_iff_edgeRootMask_card_ge_two_of_matchingCovered
    (G : BipartiteMultigraph X Y E) (hG : G.IsCubic)
    (hMC : G.IsMatchingCovered) :
    G.HasEEP ↔
      ∀ (r : X ⊕ Y) (e : E), ¬ G.Incident e r →
        2 ≤ (G.edgeRootMask r (G.portsOfCubic hG r) e).card := by
  constructor
  · intro hEEP r e hne
    exact hEEP.edgeRootMask_card_ge_two_of_cubic hG r e hne
  · intro hmask
    exact G.hasEEP_of_edgeRootMask_card_ge_two_of_matchingCovered hG hMC hmask

/-- Manuscript port-mask characterization for connected cubic bipartite
multigraphs: EEP holds exactly when every nonincident edge-root mask has at
least two ports. -/
theorem hasEEP_iff_edgeRootMask_card_ge_two
    (G : BipartiteMultigraph X Y E) (hconn : G.IsConnected) (hG : G.IsCubic) :
    G.HasEEP ↔
      ∀ (r : X ⊕ Y) (e : E), ¬ G.Incident e r →
        2 ≤ (G.edgeRootMask r (G.portsOfCubic hG r) e).card :=
  G.hasEEP_iff_edgeRootMask_card_ge_two_of_matchingCovered hG
    (G.isMatchingCovered_of_connected_cubic hconn hG)

end BipartiteMultigraph
end BachThesisLean
