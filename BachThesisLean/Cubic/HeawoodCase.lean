import BachThesisLean.Cubic.HeawoodCheck01
import BachThesisLean.Cubic.HeawoodCheck23
import BachThesisLean.Cubic.HeawoodCheck45
import BachThesisLean.Cubic.HeawoodCheck6

namespace BachThesisLean
namespace BipartiteMultigraph

/-!
# The Heawood base case

We use the standard `7 + 7` bipartite incidence presentation of the Heawood
graph.  Each left vertex `i` is adjacent to the three right vertices
`i`, `i+1`, and `i+3` modulo seven.  Actual edge copies are represented by the
left endpoint together with one of these three slots.

For EEP it is unnecessary to enumerate all perfect matchings or all subsets of
the 21 edge copies.  Eight explicit perfect matchings suffice: for every pair
of distinct prescribed copies, one of the eight omits both and its complement
contains a path of at most four edge copies between the two marked left
endpoints.  The finite verification is split by the first edge's left endpoint
across `HeawoodCheck*` modules so CI can cache the closed computation in small
pieces.
-/

/-- The eight explicit matchings cover every distinct pair of the 21 edge
copies. -/
theorem heawood_chosenMatching_works :
    ∀ e f : HeawoodEdge, e ≠ f →
      HeawoodMatchingWorks (heawoodChosenMatchingIndex e f) e f := by
  rintro ⟨i, s⟩ f hef
  fin_cases i
  · exact heawood_chosenMatching_works_left0 s f hef
  · exact heawood_chosenMatching_works_left1 s f hef
  · exact heawood_chosenMatching_works_left2 s f hef
  · exact heawood_chosenMatching_works_left3 s f hef
  · exact heawood_chosenMatching_works_left4 s f hef
  · exact heawood_chosenMatching_works_left5 s f hef
  · exact heawood_chosenMatching_works_left6 s f hef

/-- Convert the finite Heawood certificate into the generic four-edge bridge
certificate. -/
theorem heawood_fourBridgeCertificate
    (e f : HeawoodEdge) (hef : e ≠ f) :
    heawoodGraph.EdgePairFourBridgeCertificate e f := by
  let k := heawoodChosenMatchingIndex e f
  let P := heawoodCertificateMatching k
  have hP : heawoodGraph.IsPerfectMatching P := by
    simpa [P] using heawoodCertificateMatching_isPerfectMatching k
  have hworks : HeawoodMatchingWorks k e f := by
    simpa [k] using heawood_chosenMatching_works e f hef
  change e ∉ P ∧ f ∉ P ∧
    (e.1 = f.1 ∨
      ∃ x : Fin 7, ∃ s0 s1 s2 s3 : Fin 3,
        (e.1, s0) ∉ P ∧ (x, s1) ∉ P ∧
        (x, s2) ∉ P ∧ (f.1, s3) ∉ P ∧
        heawoodRight e.1 s0 = heawoodRight x s1 ∧
        heawoodRight x s2 = heawoodRight f.1 s3) at hworks
  rcases hworks with ⟨heP, hfP, hleft | hpath⟩
  · exact ⟨P, hP, heP, hfP, Or.inl hleft⟩
  · rcases hpath with ⟨x, s0, s1, s2, s3, haP, hbP, hcP, hdP, hab, hcd⟩
    let a : HeawoodEdge := (e.1, s0)
    let b : HeawoodEdge := (x, s1)
    let c : HeawoodEdge := (x, s2)
    let d : HeawoodEdge := (f.1, s3)
    refine ⟨P, hP, heP, hfP,
      Or.inr ⟨a, b, c, d, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · simpa [a] using haP
    · simpa [b] using hbP
    · simpa [c] using hcP
    · simpa [d] using hdP
    · rfl
    · simpa [a, b] using hab
    · rfl
    · simpa [c, d] using hcd
    · rfl

/-- The canonical Heawood graph has the edge-edge prescribed-component
property. -/
theorem heawoodGraph_hasEEP : heawoodGraph.HasEEP := by
  intro e f hef
  exact edgePairWitness_of_fourBridgeCertificate heawoodGraph
    (heawood_fourBridgeCertificate e f hef)

end BipartiteMultigraph
end BachThesisLean
