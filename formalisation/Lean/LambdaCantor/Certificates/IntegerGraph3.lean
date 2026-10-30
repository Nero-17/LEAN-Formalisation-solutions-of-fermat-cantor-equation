import LambdaCantor.Integer.RankedGraph

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace LambdaCantor.Integer.Band3

def edges : List ℕ := [0, 1, 2, 5, 6, 7, 8, 9, 22, 23, 24, 25, 26, 29, 34, 37, 38, 89, 90, 93, 98, 101, 102, 103, 104, 105, 118, 137, 150, 151, 152, 359, 360, 361, 374, 393, 406, 407, 408, 409, 410, 413, 418, 421, 422, 473, 550, 601, 602, 605, 610, 613, 614, 615, 616, 617, 630, 649, 662, 663, 664, 871, 872, 873, 886, 905, 918, 919, 920, 921, 922, 925, 930, 933, 934, 985, 986, 989, 994, 997, 998, 999, 1000, 1001, 1014, 1015, 1016, 1017, 1018, 1021, 1022, 1023]
def rank (v : Fin 256) : ℕ := ([0, 2, 3, 0, 0, 6, 7, 8, 9, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 17, 20, 18, 19, 0, 0, 21, 0, 0, 0, 0, 22, 0, 0, 23, 42, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 39, 35, 0, 0, 41, 0, 0, 0, 0, 42, 0, 0, 34, 32, 43, 36, 35, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 43, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 42, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 35, 37, 42, 32, 33, 0, 0, 43, 0, 0, 0, 0, 40, 0, 0, 35, 38, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 43, 24, 0, 0, 25, 0, 0, 0, 0, 31, 0, 0, 26, 27, 28, 29, 30, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11, 12, 15, 13, 14, 0, 0, 4, 5, 1] : List ℕ).getD v.val 0
def next (v : Fin 256) : Fin 256 := ⟨([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 152, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 105, 91, 92, 93, 94, 95, 96, 97, 137, 99, 100, 101, 153, 157, 104, 165, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 217, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 38, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 90, 151, 98, 102, 154, 155, 156, 118, 158, 159, 160, 161, 162, 163, 164, 150, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 103, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255] : List ℕ).getD v.val 0 % 256, Nat.mod_lt _ (by decide)⟩
def edge (v w : Fin 256) : Prop := 4 * v.val + w.val % 4 ∈ edges ∧ (4 * v.val + w.val % 4) % 256 = w.val
theorem rank_check : ∀ e : Fin 1024, e.val ∈ edges → rank ⟨e.val / 4, by omega⟩ ≤ rank ⟨e.val % 256, Nat.mod_lt _ (by decide)⟩ := by decide +kernel
theorem successor_check : ∀ e : Fin 1024, e.val ∈ edges → rank ⟨e.val / 4, by omega⟩ = rank ⟨e.val % 256, Nat.mod_lt _ (by decide)⟩ → (⟨e.val % 256, Nat.mod_lt _ (by decide)⟩ : Fin 256) = next ⟨e.val / 4, by omega⟩ := by decide +kernel
theorem next_four : ∀ v, next (next (next (next v))) = v := by decide +kernel
theorem rank_edges (v w : Fin 256) (h : edge v w) : rank v ≤ rank w := by
  have hv : 4 * v.val + w.val % 4 < 1024 := by omega
  have hdiv : (4 * v.val + w.val % 4) / 4 = v.val := by omega
  have hh := rank_check ⟨_, hv⟩ h.1
  simpa only [hdiv, h.2] using hh
theorem same_rank_edges (v w : Fin 256) (h : edge v w) (hr : rank v = rank w) : w = next v := by
  have hv : 4 * v.val + w.val % 4 < 1024 := by omega
  have hdiv : (4 * v.val + w.val % 4) / 4 = v.val := by omega
  have hh := successor_check ⟨_, hv⟩ h.1
  simpa only [hdiv, h.2] using hh (by simpa only [hdiv, h.2] using hr)
theorem eventually_period_four (path : ℕ → Fin 256) (h : ∀ n, edge (path n) (path (n+1))) : ∃ start, ∀ n ≥ start, path (n+4) = path n :=
  ranked_path_eventually_period_four edge rank next rank_edges same_rank_edges next_four path h

end LambdaCantor.Integer.Band3
