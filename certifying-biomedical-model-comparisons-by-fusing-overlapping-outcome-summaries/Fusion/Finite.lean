import Std
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
namespace FusionFinite

theorem four_record_cancellation (a b c d : Int)
(ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1)
(hc : 0 ≤ c ∧ c ≤ 1) (hd : 0 ≤ d ∧ d ≤ 1)
(h1 : a+b=1) (h2 : c+d=1) (h3 : b+d=1) (h4 : a+c=1) :
((a=1 ∧ b=0 ∧ c=0 ∧ d=1) ∨ (a=0 ∧ b=1 ∧ c=1 ∧ d=0)) ∧
(a+2*b+4*c+3*d = 3*a+2*b+4*c+d) ∧
(a+2*b+4*c+3*d = 4 ∨ a+2*b+4*c+3*d = 6) := by omega

theorem path_states_k1 (x0 x1 x2 x3 x4 x5 : Int)
 (b0 : 0 ≤ x0 ∧ x0 ≤ 1)
 (b1 : 0 ≤ x1 ∧ x1 ≤ 1)
 (b2 : 0 ≤ x2 ∧ x2 ≤ 1)
 (b3 : 0 ≤ x3 ∧ x3 ≤ 1)
 (b4 : 0 ≤ x4 ∧ x4 ≤ 1)
 (b5 : 0 ≤ x5 ∧ x5 ≤ 1)
 (cA0 : x0+x1 = 1)
 (cA1 : x2+x3+x4+x5 = 3)
 (cB0 : x0+x2+x3 = 2)
 (cB1 : x1+x4+x5 = 2)
 :
 (x0 = 1 ∧ x1 = 0 ∧ x2 = 1 ∧ x3 = 0 ∧ x4 = 1 ∧ x5 = 1) ∨
 (x0 = 1 ∧ x1 = 0 ∧ x2 = 0 ∧ x3 = 1 ∧ x4 = 1 ∧ x5 = 1) ∨
 (x0 = 0 ∧ x1 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x4 = 1 ∧ x5 = 0) ∨
 (x0 = 0 ∧ x1 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x4 = 0 ∧ x5 = 1) := by omega

#print axioms path_states_k1



-- Complete depth-two state classification with explicit case splitting.
theorem path_states_k2 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : Int)
 (b0 : 0 ≤ x0 ∧ x0 ≤ 1)
 (b1 : 0 ≤ x1 ∧ x1 ≤ 1)
 (b2 : 0 ≤ x2 ∧ x2 ≤ 1)
 (b3 : 0 ≤ x3 ∧ x3 ≤ 1)
 (b4 : 0 ≤ x4 ∧ x4 ≤ 1)
 (b5 : 0 ≤ x5 ∧ x5 ≤ 1)
 (b6 : 0 ≤ x6 ∧ x6 ≤ 1)
 (b7 : 0 ≤ x7 ∧ x7 ≤ 1)
 (b8 : 0 ≤ x8 ∧ x8 ≤ 1)
 (b9 : 0 ≤ x9 ∧ x9 ≤ 1)
 (b10 : 0 ≤ x10 ∧ x10 ≤ 1)
 (b11 : 0 ≤ x11 ∧ x11 ≤ 1)
 (b12 : 0 ≤ x12 ∧ x12 ≤ 1)
 (b13 : 0 ≤ x13 ∧ x13 ≤ 1)
 (cA0 : x0+x1 = 1)
 (cA1 : x2+x6+x7 = 1)
 (cA2 : x3+x8+x9 = 1)
 (cA3 : x4+x10+x11 = 1)
 (cA4 : x5+x12+x13 = 1)
 (cB0 : x0+x2+x3 = 2)
 (cB1 : x1+x4+x5 = 2)
 (cB2 : x6+x7+x8+x9+x10+x11+x12+x13 = 1)
 :
 (x0 = 1 ∧ x1 = 0 ∧ x2 = 0 ∧ x3 = 1 ∧ x4 = 1 ∧ x5 = 1 ∧ x6 = 0 ∧ x7 = 1 ∧ x8 = 0 ∧ x9 = 0 ∧ x10 = 0 ∧ x11 = 0 ∧ x12 = 0 ∧ x13 = 0) ∨
 (x0 = 1 ∧ x1 = 0 ∧ x2 = 0 ∧ x3 = 1 ∧ x4 = 1 ∧ x5 = 1 ∧ x6 = 1 ∧ x7 = 0 ∧ x8 = 0 ∧ x9 = 0 ∧ x10 = 0 ∧ x11 = 0 ∧ x12 = 0 ∧ x13 = 0) ∨
 (x0 = 1 ∧ x1 = 0 ∧ x2 = 1 ∧ x3 = 0 ∧ x4 = 1 ∧ x5 = 1 ∧ x6 = 0 ∧ x7 = 0 ∧ x8 = 0 ∧ x9 = 1 ∧ x10 = 0 ∧ x11 = 0 ∧ x12 = 0 ∧ x13 = 0) ∨
 (x0 = 1 ∧ x1 = 0 ∧ x2 = 1 ∧ x3 = 0 ∧ x4 = 1 ∧ x5 = 1 ∧ x6 = 0 ∧ x7 = 0 ∧ x8 = 1 ∧ x9 = 0 ∧ x10 = 0 ∧ x11 = 0 ∧ x12 = 0 ∧ x13 = 0) ∨
 (x0 = 0 ∧ x1 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x4 = 0 ∧ x5 = 1 ∧ x6 = 0 ∧ x7 = 0 ∧ x8 = 0 ∧ x9 = 0 ∧ x10 = 0 ∧ x11 = 1 ∧ x12 = 0 ∧ x13 = 0) ∨
 (x0 = 0 ∧ x1 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x4 = 0 ∧ x5 = 1 ∧ x6 = 0 ∧ x7 = 0 ∧ x8 = 0 ∧ x9 = 0 ∧ x10 = 1 ∧ x11 = 0 ∧ x12 = 0 ∧ x13 = 0) ∨
 (x0 = 0 ∧ x1 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x4 = 1 ∧ x5 = 0 ∧ x6 = 0 ∧ x7 = 0 ∧ x8 = 0 ∧ x9 = 0 ∧ x10 = 0 ∧ x11 = 0 ∧ x12 = 0 ∧ x13 = 1) ∨
 (x0 = 0 ∧ x1 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x4 = 1 ∧ x5 = 0 ∧ x6 = 0 ∧ x7 = 0 ∧ x8 = 0 ∧ x9 = 0 ∧ x10 = 0 ∧ x11 = 0 ∧ x12 = 1 ∧ x13 = 0) := by
  by_cases hr : x0 = 1
  · by_cases hc : x2 = 0
    · by_cases hp : x6 = 0
      · apply Or.inl
        repeat constructor <;> omega
      · apply Or.inr; apply Or.inl
        repeat constructor <;> omega
    · by_cases hp : x8 = 0
      · apply Or.inr; apply Or.inr; apply Or.inl
        repeat constructor <;> omega
      · apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inl
        repeat constructor <;> omega
  · by_cases hc : x4 = 0
    · by_cases hp : x10 = 0
      · apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inl
        repeat constructor <;> omega
      · apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inl
        repeat constructor <;> omega
    · by_cases hp : x12 = 0
      · apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inl
        repeat constructor <;> omega
      · apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; skip
        repeat constructor <;> omega
#print axioms path_states_k2
theorem path_states_k2_realizations : (0 ≤ (1:Int) ∧ (1:Int) ≤ 1) ∧
(0 ≤ (0:Int) ∧ (0:Int) ≤ 1) ∧
(0 ≤ (0:Int) ∧ (0:Int) ≤ 1) ∧
(0 ≤ (1:Int) ∧ (1:Int) ≤ 1) ∧
(0 ≤ (1:Int) ∧ (1:Int) ≤ 1) ∧
(0 ≤ (1:Int) ∧ (1:Int) ≤ 1) ∧
(0 ≤ (0:Int) ∧ (0:Int) ≤ 1) ∧
(0 ≤ (1:Int) ∧ (1:Int) ≤ 1) ∧
(0 ≤ (0:Int) ∧ (0:Int) ≤ 1) ∧
(0 ≤ (0:Int) ∧ (0:Int) ≤ 1) ∧
(0 ≤ (0:Int) ∧ (0:Int) ≤ 1) ∧
(0 ≤ (0:Int) ∧ (0:Int) ≤ 1) ∧
(0 ≤ (0:Int) ∧ (0:Int) ≤ 1) ∧
(0 ≤ (0:Int) ∧ (0:Int) ≤ 1) ∧
((1:Int)+(0:Int) = 1) ∧
((0:Int)+(0:Int)+(1:Int) = 1) ∧
((1:Int)+(0:Int)+(0:Int) = 1) ∧
((1:Int)+(0:Int)+(0:Int) = 1) ∧
((1:Int)+(0:Int)+(0:Int) = 1) ∧
((1:Int)+(0:Int)+(1:Int) = 2) ∧
((0:Int)+(1:Int)+(1:Int) = 2) ∧
((0:Int)+(1:Int)+(0:Int)+(0:Int)+(0:Int)+(0:Int)+(0:Int)+(0:Int) = 1) ∧
(0 ≤ (1:Int) ∧ (1:Int) ≤ 1) ∧
(0 ≤ (0:Int) ∧ (0:Int) ≤ 1) ∧
(0 ≤ (0:Int) ∧ (0:Int) ≤ 1) ∧
(0 ≤ (1:Int) ∧ (1:Int) ≤ 1) ∧
(0 ≤ (1:Int) ∧ (1:Int) ≤ 1) ∧
(0 ≤ (1:Int) ∧ (1:Int) ≤ 1) ∧
(0 ≤ (1:Int) ∧ (1:Int) ≤ 1) ∧
(0 ≤ (0:Int) ∧ (0:Int) ≤ 1) ∧
(0 ≤ (0:Int) ∧ (0:Int) ≤ 1) ∧
(0 ≤ (0:Int) ∧ (0:Int) ≤ 1) ∧
(0 ≤ (0:Int) ∧ (0:Int) ≤ 1) ∧
(0 ≤ (0:Int) ∧ (0:Int) ≤ 1) ∧
(0 ≤ (0:Int) ∧ (0:Int) ≤ 1) ∧
(0 ≤ (0:Int) ∧ (0:Int) ≤ 1) ∧
((1:Int)+(0:Int) = 1) ∧
((0:Int)+(1:Int)+(0:Int) = 1) ∧
((1:Int)+(0:Int)+(0:Int) = 1) ∧
((1:Int)+(0:Int)+(0:Int) = 1) ∧
((1:Int)+(0:Int)+(0:Int) = 1) ∧
((1:Int)+(0:Int)+(1:Int) = 2) ∧
((0:Int)+(1:Int)+(1:Int) = 2) ∧
((1:Int)+(0:Int)+(0:Int)+(0:Int)+(0:Int)+(0:Int)+(0:Int)+(0:Int) = 1) ∧
(0 ≤ (1:Int) ∧ (1:Int) ≤ 1) ∧
(0 ≤ (0:Int) ∧ (0:Int) ≤ 1) ∧
(0 ≤ (1:Int) ∧ (1:Int) ≤ 1) ∧
(0 ≤ (0:Int) ∧ (0:Int) ≤ 1) ∧
(0 ≤ (1:Int) ∧ (1:Int) ≤ 1) ∧
(0 ≤ (1:Int) ∧ (1:Int) ≤ 1) ∧
(0 ≤ (0:Int) ∧ (0:Int) ≤ 1) ∧
(0 ≤ (0:Int) ∧ (0:Int) ≤ 1) ∧
(0 ≤ (0:Int) ∧ (0:Int) ≤ 1) ∧
(0 ≤ (1:Int) ∧ (1:Int) ≤ 1) ∧
(0 ≤ (0:Int) ∧ (0:Int) ≤ 1) ∧
(0 ≤ (0:Int) ∧ (0:Int) ≤ 1) ∧
(0 ≤ (0:Int) ∧ (0:Int) ≤ 1) ∧
(0 ≤ (0:Int) ∧ (0:Int) ≤ 1) ∧
((1:Int)+(0:Int) = 1) ∧
((1:Int)+(0:Int)+(0:Int) = 1) ∧
((0:Int)+(0:Int)+(1:Int) = 1) ∧
((1:Int)+(0:Int)+(0:Int) = 1) ∧
((1:Int)+(0:Int)+(0:Int) = 1) ∧
((1:Int)+(1:Int)+(0:Int) = 2) ∧
((0:Int)+(1:Int)+(1:Int) = 2) ∧
((0:Int)+(0:Int)+(0:Int)+(1:Int)+(0:Int)+(0:Int)+(0:Int)+(0:Int) = 1) ∧
(0 ≤ (1:Int) ∧ (1:Int) ≤ 1) ∧
(0 ≤ (0:Int) ∧ (0:Int) ≤ 1) ∧
(0 ≤ (1:Int) ∧ (1:Int) ≤ 1) ∧
(0 ≤ (0:Int) ∧ (0:Int) ≤ 1) ∧
(0 ≤ (1:Int) ∧ (1:Int) ≤ 1) ∧
(0 ≤ (1:Int) ∧ (1:Int) ≤ 1) ∧
(0 ≤ (0:Int) ∧ (0:Int) ≤ 1) ∧
(0 ≤ (0:Int) ∧ (0:Int) ≤ 1) ∧
(0 ≤ (1:Int) ∧ (1:Int) ≤ 1) ∧
(0 ≤ (0:Int) ∧ (0:Int) ≤ 1) ∧
(0 ≤ (0:Int) ∧ (0:Int) ≤ 1) ∧
(0 ≤ (0:Int) ∧ (0:Int) ≤ 1) ∧
(0 ≤ (0:Int) ∧ (0:Int) ≤ 1) ∧
(0 ≤ (0:Int) ∧ (0:Int) ≤ 1) ∧
((1:Int)+(0:Int) = 1) ∧
((1:Int)+(0:Int)+(0:Int) = 1) ∧
((0:Int)+(1:Int)+(0:Int) = 1) ∧
((1:Int)+(0:Int)+(0:Int) = 1) ∧
((1:Int)+(0:Int)+(0:Int) = 1) ∧
((1:Int)+(1:Int)+(0:Int) = 2) ∧
((0:Int)+(1:Int)+(1:Int) = 2) ∧
((0:Int)+(0:Int)+(1:Int)+(0:Int)+(0:Int)+(0:Int)+(0:Int)+(0:Int) = 1) ∧
(0 ≤ (0:Int) ∧ (0:Int) ≤ 1) ∧
(0 ≤ (1:Int) ∧ (1:Int) ≤ 1) ∧
(0 ≤ (1:Int) ∧ (1:Int) ≤ 1) ∧
(0 ≤ (1:Int) ∧ (1:Int) ≤ 1) ∧
(0 ≤ (0:Int) ∧ (0:Int) ≤ 1) ∧
(0 ≤ (1:Int) ∧ (1:Int) ≤ 1) ∧
(0 ≤ (0:Int) ∧ (0:Int) ≤ 1) ∧
(0 ≤ (0:Int) ∧ (0:Int) ≤ 1) ∧
(0 ≤ (0:Int) ∧ (0:Int) ≤ 1) ∧
(0 ≤ (0:Int) ∧ (0:Int) ≤ 1) ∧
(0 ≤ (0:Int) ∧ (0:Int) ≤ 1) ∧
(0 ≤ (1:Int) ∧ (1:Int) ≤ 1) ∧
(0 ≤ (0:Int) ∧ (0:Int) ≤ 1) ∧
(0 ≤ (0:Int) ∧ (0:Int) ≤ 1) ∧
((0:Int)+(1:Int) = 1) ∧
((1:Int)+(0:Int)+(0:Int) = 1) ∧
((1:Int)+(0:Int)+(0:Int) = 1) ∧
((0:Int)+(0:Int)+(1:Int) = 1) ∧
((1:Int)+(0:Int)+(0:Int) = 1) ∧
((0:Int)+(1:Int)+(1:Int) = 2) ∧
((1:Int)+(0:Int)+(1:Int) = 2) ∧
((0:Int)+(0:Int)+(0:Int)+(0:Int)+(0:Int)+(1:Int)+(0:Int)+(0:Int) = 1) ∧
(0 ≤ (0:Int) ∧ (0:Int) ≤ 1) ∧
(0 ≤ (1:Int) ∧ (1:Int) ≤ 1) ∧
(0 ≤ (1:Int) ∧ (1:Int) ≤ 1) ∧
(0 ≤ (1:Int) ∧ (1:Int) ≤ 1) ∧
(0 ≤ (0:Int) ∧ (0:Int) ≤ 1) ∧
(0 ≤ (1:Int) ∧ (1:Int) ≤ 1) ∧
(0 ≤ (0:Int) ∧ (0:Int) ≤ 1) ∧
(0 ≤ (0:Int) ∧ (0:Int) ≤ 1) ∧
(0 ≤ (0:Int) ∧ (0:Int) ≤ 1) ∧
(0 ≤ (0:Int) ∧ (0:Int) ≤ 1) ∧
(0 ≤ (1:Int) ∧ (1:Int) ≤ 1) ∧
(0 ≤ (0:Int) ∧ (0:Int) ≤ 1) ∧
(0 ≤ (0:Int) ∧ (0:Int) ≤ 1) ∧
(0 ≤ (0:Int) ∧ (0:Int) ≤ 1) ∧
((0:Int)+(1:Int) = 1) ∧
((1:Int)+(0:Int)+(0:Int) = 1) ∧
((1:Int)+(0:Int)+(0:Int) = 1) ∧
((0:Int)+(1:Int)+(0:Int) = 1) ∧
((1:Int)+(0:Int)+(0:Int) = 1) ∧
((0:Int)+(1:Int)+(1:Int) = 2) ∧
((1:Int)+(0:Int)+(1:Int) = 2) ∧
((0:Int)+(0:Int)+(0:Int)+(0:Int)+(1:Int)+(0:Int)+(0:Int)+(0:Int) = 1) ∧
(0 ≤ (0:Int) ∧ (0:Int) ≤ 1) ∧
(0 ≤ (1:Int) ∧ (1:Int) ≤ 1) ∧
(0 ≤ (1:Int) ∧ (1:Int) ≤ 1) ∧
(0 ≤ (1:Int) ∧ (1:Int) ≤ 1) ∧
(0 ≤ (1:Int) ∧ (1:Int) ≤ 1) ∧
(0 ≤ (0:Int) ∧ (0:Int) ≤ 1) ∧
(0 ≤ (0:Int) ∧ (0:Int) ≤ 1) ∧
(0 ≤ (0:Int) ∧ (0:Int) ≤ 1) ∧
(0 ≤ (0:Int) ∧ (0:Int) ≤ 1) ∧
(0 ≤ (0:Int) ∧ (0:Int) ≤ 1) ∧
(0 ≤ (0:Int) ∧ (0:Int) ≤ 1) ∧
(0 ≤ (0:Int) ∧ (0:Int) ≤ 1) ∧
(0 ≤ (0:Int) ∧ (0:Int) ≤ 1) ∧
(0 ≤ (1:Int) ∧ (1:Int) ≤ 1) ∧
((0:Int)+(1:Int) = 1) ∧
((1:Int)+(0:Int)+(0:Int) = 1) ∧
((1:Int)+(0:Int)+(0:Int) = 1) ∧
((1:Int)+(0:Int)+(0:Int) = 1) ∧
((0:Int)+(0:Int)+(1:Int) = 1) ∧
((0:Int)+(1:Int)+(1:Int) = 2) ∧
((1:Int)+(1:Int)+(0:Int) = 2) ∧
((0:Int)+(0:Int)+(0:Int)+(0:Int)+(0:Int)+(0:Int)+(0:Int)+(1:Int) = 1) ∧
(0 ≤ (0:Int) ∧ (0:Int) ≤ 1) ∧
(0 ≤ (1:Int) ∧ (1:Int) ≤ 1) ∧
(0 ≤ (1:Int) ∧ (1:Int) ≤ 1) ∧
(0 ≤ (1:Int) ∧ (1:Int) ≤ 1) ∧
(0 ≤ (1:Int) ∧ (1:Int) ≤ 1) ∧
(0 ≤ (0:Int) ∧ (0:Int) ≤ 1) ∧
(0 ≤ (0:Int) ∧ (0:Int) ≤ 1) ∧
(0 ≤ (0:Int) ∧ (0:Int) ≤ 1) ∧
(0 ≤ (0:Int) ∧ (0:Int) ≤ 1) ∧
(0 ≤ (0:Int) ∧ (0:Int) ≤ 1) ∧
(0 ≤ (0:Int) ∧ (0:Int) ≤ 1) ∧
(0 ≤ (0:Int) ∧ (0:Int) ≤ 1) ∧
(0 ≤ (1:Int) ∧ (1:Int) ≤ 1) ∧
(0 ≤ (0:Int) ∧ (0:Int) ≤ 1) ∧
((0:Int)+(1:Int) = 1) ∧
((1:Int)+(0:Int)+(0:Int) = 1) ∧
((1:Int)+(0:Int)+(0:Int) = 1) ∧
((1:Int)+(0:Int)+(0:Int) = 1) ∧
((0:Int)+(1:Int)+(0:Int) = 1) ∧
((0:Int)+(1:Int)+(1:Int) = 2) ∧
((1:Int)+(1:Int)+(0:Int) = 2) ∧
((0:Int)+(0:Int)+(0:Int)+(0:Int)+(0:Int)+(0:Int)+(1:Int)+(0:Int) = 1) := by
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
#print axioms path_states_k2_realizations


theorem ranks_k1 :
 ([5,6,1,2,3,4] : List Int).Perm (List.range' 1 6 |>.map Int.ofNat) ∧
 ([5,6,2,1,4,3] : List Int).Perm (List.range' 1 6 |>.map Int.ofNat) ∧
 List.zipWith (fun (a b : Int) => a-b) [5,6,1,2,3,4] [5,6,2,1,4,3] = [0,0,-1,1,-1,1] := by
  exact ⟨by decide, by decide, by decide⟩

theorem distinct_states_k1 :
 ([[1,0,1,0,1,1],[1,0,0,1,1,1],[0,1,1,1,1,0],[0,1,1,1,0,1]] : List (List Int)).Nodup := by decide

theorem ranks_k2 :
 ([9,10,11,12,13,14,2,1,4,3,6,5,8,7] : List Int).Perm (List.range' 1 14 |>.map Int.ofNat) ∧
 ([9,10,11,12,13,14,1,2,3,4,5,6,7,8] : List Int).Perm (List.range' 1 14 |>.map Int.ofNat) ∧
 List.zipWith (fun (a b : Int) => a-b) [9,10,11,12,13,14,2,1,4,3,6,5,8,7] [9,10,11,12,13,14,1,2,3,4,5,6,7,8] = [0,0,0,0,0,0,1,-1,1,-1,1,-1,1,-1] := by
  exact ⟨by decide, by decide, by decide⟩

theorem distinct_states_k2 :
 ([[1,0,0,1,1,1,0,1,0,0,0,0,0,0],[1,0,0,1,1,1,1,0,0,0,0,0,0,0],[1,0,1,0,1,1,0,0,0,1,0,0,0,0],[1,0,1,0,1,1,0,0,1,0,0,0,0,0],[0,1,1,1,0,1,0,0,0,0,0,1,0,0],[0,1,1,1,0,1,0,0,0,0,1,0,0,0],[0,1,1,1,1,0,0,0,0,0,0,0,0,1],[0,1,1,1,1,0,0,0,0,0,0,0,1,0]] : List (List Int)).Nodup := by decide

end FusionFinite
