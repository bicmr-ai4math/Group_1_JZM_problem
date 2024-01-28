-- 五点共圆（JZM问题）
-- 林元莘 王孙葳 上海交通大学

import EuclideanGeometry.Foundation.Index

noncomputable section

namespace EuclidGeom

variable {Plane : Type _} [EuclideanPlane Plane]

-- There are temporarily no functions for the circumcircle of three points and the perpendicular bisector before the completion of this section of the code.
-- We dicide to creat one.

-- Perpendicular bisector

def perp_bis (A B : Plane)(h: B ≠ A) : Line Plane :=
  perp_line ((SEG A B).midpoint) (LIN A B h)

-- The points on the perpendicular bisector of a line segment are equidistant from the two endpoints.
-- We haven't complete that yet.
theorem dist_eq_of_on_perp_bis {A B C : Plane} (h: B ≠ A) (h1: C LiesOn perp_bis A B h) :
   dist A C = dist B C := by sorry

-- The circumcenter of a triangle is the intersection point of the perpendicular bisectors of any two sides.

def circumcenter (tr : TriangleND Plane) : Plane :=
-- Annoying collinearity
  have tr_bis_intersect : ¬ (perp_bis tr.1.1 tr.1.2 (ne_of_not_collinear tr.2).2.2) ∥ (perp_bis tr.1.2 tr.1.3 (ne_of_not_collinear tr.2).1) := sorry
  Line.inx (perp_bis tr.1.1 tr.1.2 (ne_of_not_collinear tr.2).2.2) (perp_bis tr.1.2 tr.1.3 (ne_of_not_collinear tr.2).1) tr_bis_intersect

-- The circumcenter of a triangle is equidistant from the three vertices.
theorem circumcenter_dist_vetex_eq {tr : TriangleND Plane}: dist tr.1.1 (circumcenter tr) = dist tr.1.2 (circumcenter tr) ∧ dist tr.1.2 (circumcenter tr) = dist tr.1.3 (circumcenter tr) ∧ dist tr.1.1 (circumcenter tr) = dist tr.1.3 (circumcenter tr) := by

  have O1_eq_O2 : dist tr.1.1 (circumcenter tr) = dist tr.1.2 (circumcenter tr) := by
    apply dist_eq_of_on_perp_bis (ne_of_not_collinear tr.2).2.2 _
    have tr_bis_intersect : ¬ (perp_bis tr.1.1 tr.1.2 (ne_of_not_collinear tr.2).2.2) ∥ (perp_bis tr.1.2 tr.1.3 (ne_of_not_collinear tr.2).1) := sorry
    rw[circumcenter]
    apply Line.inx_lies_on_fst tr_bis_intersect
  have O2_eq_O3 : dist tr.1.2 (circumcenter tr) = dist tr.1.3 (circumcenter tr) := by
    apply dist_eq_of_on_perp_bis (ne_of_not_collinear tr.2).1 _
    have tr_bis_intersect : ¬ (perp_bis tr.1.1 tr.1.2 (ne_of_not_collinear tr.2).2.2) ∥ (perp_bis tr.1.2 tr.1.3 (ne_of_not_collinear tr.2).1) := sorry
    rw[circumcenter]
    apply Line.inx_lies_on_snd tr_bis_intersect
  constructor
  exact O1_eq_O2
  constructor
  exact O2_eq_O3
  rw[O1_eq_O2, O2_eq_O3]

-- Annoying Non-zero
theorem circum_not_vertex {tr : TriangleND Plane}: 0 < dist (circumcenter tr) tr.1.1 ∧ 0 < dist tr.1.2 (circumcenter tr)  ∧0 <  dist tr.1.3 (circumcenter tr) := by
  sorry


-- Three non-collinear points determine a circle.

def mk_pt_pt_pt_circle (A B C : Plane) (h: ¬Collinear A B C) : Circle Plane where
  center := circumcenter (TRI_nd A B C h)
  radius := dist (circumcenter (TRI_nd A B C h)) A
  rad_pos := by
    let tr := TRI_nd A B C h
    have h₁ : 0 < dist (circumcenter tr) tr.1.1 := by exact (circum_not_vertex).1
    exact h₁

-- Several useful but annoying theorems



-- Points lies on the circle we made.
theorem pt_on_mk_pt_pt_pt_circle {A B C : Plane} (h: ¬Collinear A B C) : A LiesOn mk_pt_pt_pt_circle A B C h ∧ B LiesOn mk_pt_pt_pt_circle A B C h ∧ C LiesOn mk_pt_pt_pt_circle A B C h :=by
  constructor
  rfl
  constructor
  have h₁ : dist A (circumcenter (TRI_nd A B C h)) = dist B (circumcenter (TRI_nd A B C h)) := by
    have q₁ : A = (TRI_nd A B C h).1.1 := by rfl
    have q₂ : B = (TRI_nd A B C h).1.2 := by rfl
    nth_rw 1 [q₁]
    nth_rw 3 [q₂]
    sorry
  sorry
  sorry



-- Criterion for four points to be concyclic
theorem four_pt_circle {A B C D : Plane} (h₁ : ¬Collinear A B C) (h₂ : A ≠ D) (h₃ : C ≠ D) (hang : (ANG A B C (ne_of_not_collinear h₁).2.2.symm  (ne_of_not_collinear h₁).1).dvalue = (ANG A D C h₂ h₃).dvalue) : D LiesOn mk_pt_pt_pt_circle A B C h₁ := by
  sorry
-- One side of the two angles is collinear.
theorem dvalue_eq_dir1_one_line {A B O Q : Plane} (l : Line Plane) (h : A LiesOn l ∧ B LiesOn l ∧ O LiesOn l)(h₁: ¬ Collinear A O Q) (h₂ : ¬ Collinear B O Q) : (ANG A O Q (ne_of_not_collinear h₁).2.2.symm  (ne_of_not_collinear h₁).1).dvalue = (ANG B O Q (ne_of_not_collinear h₂).2.2.symm  (ne_of_not_collinear h₂).1).dvalue := by
  sorry

theorem dvalue_eq_dir2_one_line {A B O Q : Plane} (l : Line Plane) (h : A LiesOn l ∧ B LiesOn l ∧ O LiesOn l)(h₁: ¬ Collinear Q O A) (h₂ : ¬ Collinear Q O B) : (ANG Q O A (ne_of_not_collinear h₁).2.2.symm  (ne_of_not_collinear h₁).1).dvalue = (ANG Q O B (ne_of_not_collinear h₂).2.2.symm  (ne_of_not_collinear h₂).1).dvalue := by
  sorry

-- Inscribed angles are equal modulo π.
theorem iangle_theorem {A B C D : Plane} (O : Circle Plane) (h₁ : ¬ Collinear A B C) (h₂ : ¬ Collinear A D C) (hc : A LiesOn O ∧ B LiesOn O ∧ C LiesOn O ∧ D LiesOn O) : (ANG A B C (ne_of_not_collinear h₁).2.2.symm  (ne_of_not_collinear h₁).1).dvalue = (ANG A D C (ne_of_not_collinear h₂).2.2.symm  (ne_of_not_collinear h₂).1).dvalue := by
  sorry

-- addition for angles with a common vertex.
theorem dvalue_add_theorem {A B C O : Plane} (h₁ : ¬ Collinear A O B) (h₂ : ¬ Collinear A O C) (h₃ : ¬ Collinear C O B) :
(ANG A O B (ne_of_not_collinear h₁).2.2.symm (ne_of_not_collinear h₁).1).dvalue = (ANG A O C (ne_of_not_collinear h₂).2.2.symm (ne_of_not_collinear h₂).1).dvalue + (ANG C O B (ne_of_not_collinear h₃).2.2.symm (ne_of_not_collinear h₃).1).dvalue := by
sorry

-- Now we start creating the STAR.
structure Setting (Plane : Type _) [EuclideanPlane Plane] where
-- Firstly, we creat 5 points to generate a Pentagon ABCDE.
  A : Plane
  B : Plane
  C : Plane
  D : Plane
  E : Plane
  B_ne_A : B ≠ A
  C_ne_B : C ≠ B
  D_ne_C : D ≠ C
  E_ne_D : E ≠ D
  A_ne_E : A ≠ E
-- These ensure that the pentagon is non-degenerate.
  hp₁ : ¬ Collinear A B C
  hp₂ : ¬ Collinear B C D
  hp₃ : ¬ Collinear C D E
  hp₄ : ¬ Collinear D E A
  hp₅ : ¬ Collinear E A B
  l₁ := LIN A B B_ne_A
  l₂ := LIN B C C_ne_B
  l₃ := LIN C D D_ne_C
  l₄ := LIN D E E_ne_D
  l₅ := LIN E A A_ne_E
-- Non-parallelism ensures the creation of a STAR FGHIJ-ABCDE.
  h₁ : ¬ l₁ ∥ l₃
  h₂ : ¬ l₂ ∥ l₄
  h₃ : ¬ l₃ ∥ l₅
  h₄ : ¬ l₄ ∥ l₁
  h₅ : ¬ l₅ ∥ l₂
  F : Plane
  G : Plane
  H : Plane
  I : Plane
  J : Plane
  F_inx : is_inx F l₁ l₃
  G_inx : is_inx G l₂ l₄
  H_inx : is_inx H l₃ l₅
  I_inx : is_inx I l₄ l₁
  J_inx : is_inx J l₅ l₂
-- Some conditions for laziness
  IBF_on_l₁ : I LiesOn l₁ ∧ B LiesOn l₁ ∧ F LiesOn l₁ := by sorry
  IBA_on_l₁ : I LiesOn l₁ ∧ B LiesOn l₁ ∧ A LiesOn l₁ := by sorry
  BGC_on_l₂ : B LiesOn l₂ ∧ G LiesOn l₂ ∧ C LiesOn l₂ := by sorry
  GID_on_l₄ : G LiesOn l₄ ∧ I LiesOn l₄ ∧ D LiesOn l₄ := by sorry
  hF : ¬ Collinear B C F := by sorry
  hG : ¬ Collinear C D G := by sorry
  hH : ¬ Collinear D E H := by sorry
  hI : ¬ Collinear E A I := by sorry
  hJ : ¬ Collinear A B J := by sorry
  tr₁ := TRI_nd B C F hF
  tr₂ := TRI_nd C D G hG
  tr₃ := TRI_nd D E H hH
  tr₄ := TRI_nd E A I hI
  tr₅ := TRI_nd A B J hJ
-- Creat 5 circles
  C₁ : Circle Plane
  hc1 : C₁ = mk_pt_pt_pt_circle B C F hF
  C₂ : Circle Plane
  hc2 : C₂ = mk_pt_pt_pt_circle C D G hG
  C₃ : Circle Plane
  hc3 : C₃ = mk_pt_pt_pt_circle D E H hH
  C₄ : Circle Plane
  hc4 : C₄ = mk_pt_pt_pt_circle E A I hI
  C₅ : Circle Plane
  hc5 : C₅ = mk_pt_pt_pt_circle A B J hJ
  c₁intc₂ : C₁ Intersect C₂
  c₂intc₃ : C₂ Intersect C₃
  c₃intc₄ : C₃ Intersect C₄
  c₄intc₅ : C₄ Intersect C₅
  c₅intc₁ : C₅ Intersect C₁
  K : Plane
  hK : K LiesOn C₅ ∧ K LiesOn C₁ ∧ K ≠ B
  L : Plane
  hL : L LiesOn C₁ ∧ L LiesOn C₂ ∧ L ≠ C
  M : Plane
  hM : M LiesOn C₂ ∧ M LiesOn C₃ ∧ M ≠ D
  N : Plane
  hN : N LiesOn C₃ ∧ N LiesOn C₄ ∧ N ≠ E
  O : Plane
  hP : O LiesOn C₄ ∧ O LiesOn C₅ ∧ O ≠ A
-- Some conditions for laziness
  BFLC_on_C₁ : B LiesOn C₁ ∧ F LiesOn C₁ ∧ L LiesOn C₁ ∧ C LiesOn C₁ := by sorry
  LKBF_on_C₁ : L LiesOn C₁ ∧ K LiesOn C₁ ∧ B LiesOn C₁ ∧ F LiesOn C₁ := by sorry
  GDLC_on_C₂ : G LiesOn C₂ ∧ D LiesOn C₂ ∧ L LiesOn C₂ ∧ C LiesOn C₂ := by sorry
  INOA_on_C₄ : I LiesOn C₄ ∧ N LiesOn C₄ ∧ O LiesOn C₄ ∧ A LiesOn C₄ := by sorry
  BKOA_on_C₅ : B LiesOn C₅ ∧ K LiesOn C₅ ∧ O LiesOn C₅ ∧ A LiesOn C₅ := by sorry
  IFL : ¬ Collinear I F L := by sorry
  LKO : ¬ Collinear L K O := by sorry
  IDL : ¬ Collinear I D L := by sorry
  BFL : ¬ Collinear B F L := by sorry
  BCL : ¬ Collinear B C L := by sorry
  GDL : ¬ Collinear G D L := by sorry
  LKB : ¬ Collinear L K B := by sorry
  BKO : ¬ Collinear B K O := by sorry
  LFI : ¬ Collinear L F I := by sorry
  BAO : ¬ Collinear B A O := by sorry
  LNO : ¬ Collinear L N O := by sorry
  LNI : ¬ Collinear L N I := by sorry
  INO : ¬ Collinear I N O := by sorry
  GCL : ¬ Collinear G C L := by sorry
  LFB : ¬ Collinear L F B := by sorry
  IAO : ¬ Collinear I A O := by sorry

-- Restate our problem : A STAR FGHIJ-ABCDE, create circumcircles of 5 triangles : C₁ for ▵BCF, C₂ for ▵CDG, C₃ for ▵DHE,
-- C₄ for ▵EAI, C₅ for ▵ABJ. Two adjacent circles intersect at two different points : K,B ∈ C₅ ∩ C₁, L,C ∈ C₁ ∩ C₂, M,D ∈ C₂ ∩ C₃, N,E ∈ C₃ ∩ C₄, O,A ∈ C₄ ∩ C₅
-- Prove: K,L,M,N,O are concyclic

theorem JZM_Theorem {Plane : Type _} [EuclideanPlane Plane] (e : Setting Plane): ∃ (X : Circle Plane), e.K LiesOn X ∧ e.L LiesOn X ∧ e.M LiesOn X ∧ e.N LiesOn X ∧ e.O LiesOn X := by
-- First, we prove that I,F,L,D are concyclic
  have IFLD_c : e.D LiesOn mk_pt_pt_pt_circle e.I e.F e.L e.IFL := by
  -- Prove ∠IFL = ∠GDL (mod π) (the equalities below are under the meaning of modulo π)
    have IFL_eq_GDL : (ANG e.I e.F e.L (ne_of_not_collinear e.IFL).2.2.symm  (ne_of_not_collinear e.IFL).1).dvalue = (ANG e.I e.D e.L (ne_of_not_collinear e.IDL).2.2.symm  (ne_of_not_collinear e.IDL).1).dvalue := by
    -- We can prove it by ∠IFL = ∠BCL = ∠GCL = ∠GDL
      -- Prove ∠IFL = ∠BFL by collinearity.
      have s₁ : (ANG e.I e.F e.L (ne_of_not_collinear e.IFL).2.2.symm  (ne_of_not_collinear e.IFL).1).dvalue = (ANG e.B e.F e.L (ne_of_not_collinear e.BFL).2.2.symm  (ne_of_not_collinear e.BFL).1).dvalue := by
        exact dvalue_eq_dir1_one_line e.l₁ e.IBF_on_l₁ e.IFL e.BFL
      -- Prove ∠BFL = ∠BCL by concyclicity
      have s₂ : (ANG e.B e.F e.L (ne_of_not_collinear e.BFL).2.2.symm  (ne_of_not_collinear e.BFL).1).dvalue = (ANG e.B e.C e.L (ne_of_not_collinear e.BCL).2.2.symm  (ne_of_not_collinear e.BCL).1).dvalue := by
        exact iangle_theorem e.C₁ e.BFL e.BCL e.BFLC_on_C₁
      -- Prove ∠BCL = ∠ GCL by collinearity
      have s₃ : (ANG e.B e.C e.L (ne_of_not_collinear e.BCL).2.2.symm  (ne_of_not_collinear e.BCL).1).dvalue = (ANG e.G e.D e.L (ne_of_not_collinear e.GDL).2.2.symm  (ne_of_not_collinear e.GDL).1).dvalue := by
        rw [iangle_theorem e.C₂ e.GDL e.GCL e.GDLC_on_C₂]
        exact dvalue_eq_dir1_one_line e.l₂ e.BGC_on_l₂ e.BCL e.GCL
      rw[s₁,s₂,s₃]
      exact dvalue_eq_dir1_one_line e.l₄ e.GID_on_l₄ e.GDL e.IDL
    exact four_pt_circle (e.IFL) (ne_of_not_collinear e.IDL).2.2.symm (ne_of_not_collinear e.IDL).1 IFL_eq_GDL
  -- Prove I,F,N,L are concyclic. Only need to prove ∠FIN = ∠FDN as above.
  have IFNL_c : e.N LiesOn mk_pt_pt_pt_circle e.I e.F e.L e.IFL := by sorry
-- Second, we have I,F,N,L,D are concyclic. We can prove that K,L,O,N are concyclic.
  have KLON_c : e.N LiesOn mk_pt_pt_pt_circle e.L e.K e.O e.LKO := by
    let aLFI := (ANG e.L e.F e.I (ne_of_not_collinear e.LFI).2.2.symm  (ne_of_not_collinear e.LFI).1)
    let aBAO := (ANG e.B e.A e.O (ne_of_not_collinear e.BAO).2.2.symm  (ne_of_not_collinear e.BAO).1)
    let aLNO := (ANG e.L e.N e.O (ne_of_not_collinear e.LNO).2.2.symm  (ne_of_not_collinear e.LNO).1)
    let aLNI := (ANG e.L e.N e.I (ne_of_not_collinear e.LNI).2.2.symm  (ne_of_not_collinear e.LNI).1)
    let aINO := (ANG e.I e.N e.O (ne_of_not_collinear e.INO).2.2.symm  (ne_of_not_collinear e.INO).1)
  -- Prove ∠LKO = ∠LNO
    -- Prove ∠LKO = ∠LKB + ∠BKO = ∠LFI + ∠BAO
    have LKO_eq_LFI_ad_BAO : (ANG e.L e.K e.O (ne_of_not_collinear e.LKO).2.2.symm  (ne_of_not_collinear e.LKO).1).dvalue = (ANG e.L e.F e.I (ne_of_not_collinear e.LFI).2.2.symm  (ne_of_not_collinear e.LFI).1).dvalue + (ANG e.B e.A e.O (ne_of_not_collinear e.BAO).2.2.symm  (ne_of_not_collinear e.BAO).1).dvalue := by
      -- Prove ∠LKB = ∠LFI
      have LKB_eq_LFI : (ANG e.L e.K e.B (ne_of_not_collinear e.LKB).2.2.symm  (ne_of_not_collinear e.LKB).1).dvalue = (ANG e.L e.F e.I (ne_of_not_collinear e.LFI).2.2.symm  (ne_of_not_collinear e.LFI).1).dvalue := by
        rw[dvalue_eq_dir2_one_line e.l₁ e.IBF_on_l₁ e.LFI e.LFB] --∠LFI = ∠LFB
        exact iangle_theorem e.C₁ e.LKB e.LFB e.LKBF_on_C₁ -- ∠LKB = ∠LFB
      -- Prove ∠BKO = ∠BAO by concyclicity
      have BKO_eq_BAO : (ANG e.B e.K e.O (ne_of_not_collinear e.BKO).2.2.symm  (ne_of_not_collinear e.BKO).1).dvalue = (ANG e.B e.A e.O (ne_of_not_collinear e.BAO).2.2.symm  (ne_of_not_collinear e.BAO).1).dvalue := by
        exact iangle_theorem e.C₅ e.BKO e.BAO e.BKOA_on_C₅
      -- Prove ∠LKO = ∠LKB + ∠BKO
      have LKO_eq_LKB_ad_BKO : (ANG e.L e.K e.O (ne_of_not_collinear e.LKO).2.2.symm  (ne_of_not_collinear e.LKO).1).dvalue = (ANG e.L e.K e.B (ne_of_not_collinear e.LKB).2.2.symm  (ne_of_not_collinear e.LKB).1).dvalue + (ANG e.B e.K e.O (ne_of_not_collinear e.BKO).2.2.symm  (ne_of_not_collinear e.BKO).1).dvalue := by
        exact dvalue_add_theorem e.LKO e.LKB e.BKO
      rw[LKB_eq_LFI.symm,BKO_eq_BAO.symm,LKO_eq_LKB_ad_BKO]
    have LKO_eq_LNO : (ANG e.L e.K e.O (ne_of_not_collinear e.LKO).2.2.symm  (ne_of_not_collinear e.LKO).1).dvalue = (ANG e.L e.N e.O (ne_of_not_collinear e.LNO).2.2.symm  (ne_of_not_collinear e.LNO).1).dvalue := by
      -- Prove ∠LNO = ∠LNI + ∠INO
      have LNO_eq_LNI_ad_INO : aLNO.dvalue = aLNI.dvalue + aINO.dvalue := by
        exact dvalue_add_theorem e.LNO e.LNI e.INO
      -- Prove ∠LNI = ∠LFI
      have LNI_eq_LFI : aLNI.dvalue = aLFI.dvalue := by
        apply iangle_theorem (mk_pt_pt_pt_circle e.I e.F e.L e.IFL) e.LNI e.LFI _
        constructor
        exact (pt_on_mk_pt_pt_pt_circle e.IFL).2.2
        constructor
        exact IFNL_c
        constructor
        exact (pt_on_mk_pt_pt_pt_circle e.IFL).1
        exact (pt_on_mk_pt_pt_pt_circle e.IFL).2.1
      -- Prove ∠INO = ∠BAO
      have INO_eq_BAO : aINO.dvalue = aBAO.dvalue := by
        rw [iangle_theorem e.C₄ e.INO e.IAO e.INOA_on_C₄]
        exact dvalue_eq_dir1_one_line e.l₁ e.IBA_on_l₁ e.IAO e.BAO
      rw[LKO_eq_LFI_ad_BAO,LNI_eq_LFI.symm,INO_eq_BAO.symm,LNO_eq_LNI_ad_INO]
    exact four_pt_circle (e.LKO) (ne_of_not_collinear e.LNO).2.2.symm (ne_of_not_collinear e.LNO).1 LKO_eq_LNO
  -- In the same way, we can prove L,K,O,M are concyclicity
  have LKOM_c : e.M LiesOn mk_pt_pt_pt_circle e.L e.K e.O e.LKO := by sorry
  -- Give a conclusion
  use mk_pt_pt_pt_circle e.L e.K e.O e.LKO
  constructor
  exact (pt_on_mk_pt_pt_pt_circle e.LKO).2.1
  constructor
  exact (pt_on_mk_pt_pt_pt_circle e.LKO).1
  constructor
  exact LKOM_c
  constructor
  exact KLON_c
  exact (pt_on_mk_pt_pt_pt_circle e.LKO).2.2
