import LambdaCantor.Integer.RankedGraph

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace LambdaCantor.Integer.Band1

def edges : List ℕ := [0, 1, 2, 3, 4, 11, 12, 13, 14, 17, 18, 19, 44, 45, 46, 49, 50, 51, 52, 59, 68, 75, 76, 179, 180, 187, 196, 203, 204, 205, 206, 209, 210, 211, 236, 275, 300, 301, 302, 305, 718, 721, 722, 723, 748, 787, 812, 813, 814, 817, 818, 819, 820, 827, 836, 843, 844, 947, 948, 955, 964, 971, 972, 973, 974, 977, 978, 979, 1004, 1005, 1006, 1009, 1010, 1011, 1012, 1019, 1020, 1021, 1022, 1023]
def rank (v : Fin 256) : ℕ := ([0, 3, 4, 2, 11, 0, 0, 0, 0, 0, 0, 12, 8, 9, 10, 0, 0, 18, 19, 35, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28, 27, 29, 0, 0, 35, 23, 20, 26, 0, 0, 0, 0, 0, 0, 34, 0, 0, 0, 0, 0, 0, 0, 0, 33, 0, 0, 0, 0, 0, 0, 27, 35, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 34, 27, 0, 0, 0, 0, 0, 0, 32, 0, 0, 0, 0, 0, 0, 0, 0, 35, 0, 0, 0, 0, 0, 0, 25, 20, 24, 34, 0, 0, 30, 27, 31, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 34, 21, 22, 0, 0, 13, 14, 15, 16, 0, 0, 0, 0, 0, 0, 17, 5, 6, 7, 1] : List ℕ).getD v.val 0
def next (v : Fin 256) : Fin 256 := ⟨([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 76, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 180, 46, 47, 48, 196, 50, 204, 52, 53, 54, 55, 56, 57, 58, 236, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 45, 49, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 206, 210, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 19, 197, 198, 199, 200, 201, 202, 203, 51, 205, 59, 207, 208, 209, 75, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 179, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255] : List ℕ).getD v.val 0 % 256, Nat.mod_lt _ (by decide)⟩
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

end LambdaCantor.Integer.Band1
