Bin.bin.bin_case :: "i ⇒ i ⇒ (i ⇒ i ⇒ i) ⇒ i ⇒ i"  (* uses case, split *)
Bin.bin.bin_rec :: "i ⇒ i ⇒ (i ⇒ i ⇒ i ⇒ i) ⇒ i ⇒ i" (* uses Vrecursor, bin_case *)
Cardinal.Least :: "(i ⇒ o) ⇒ i"
Datatype_absolute.contin :: "(i ⇒ i) ⇒ o"
Datatype_absolute.formula_rec_case :: "(i ⇒ i ⇒ i) ⇒ (i ⇒ i ⇒ i) ⇒ (i ⇒ i ⇒ i ⇒ i ⇒ i) ⇒ (i ⇒ i ⇒ i) ⇒ i ⇒ i ⇒ i" (* uses formula_case *)
Epsilon.rec :: "i ⇒ i ⇒ (i ⇒ i ⇒ i) ⇒ i" (* uses recursor *)
Epsilon.recursor :: "i ⇒ (i ⇒ i ⇒ i) ⇒ i ⇒ i" (* Example 2 *)
Epsilon.transrec :: "i ⇒ (i ⇒ i ⇒ i) ⇒ i"
Epsilon.transrec2 :: "i ⇒ i ⇒ (i ⇒ i ⇒ i) ⇒ i" (* uses transrec, If --- Example 3*)
EquivClass.congruent :: "i ⇒ (i ⇒ i) ⇒ o" 
EquivClass.congruent2 :: "i ⇒ i ⇒ (i ⇒ i ⇒ i) ⇒ o"
Fixedpt.bnd_mono :: "i ⇒ (i ⇒ i) ⇒ o"
Fixedpt.gfp :: "i ⇒ (i ⇒ i) ⇒ i"
Fixedpt.lfp :: "i ⇒ (i ⇒ i) ⇒ i"
Formula.formula.formula_case :: "(i ⇒ i ⇒ i) ⇒ (i ⇒ i ⇒ i) ⇒ (i ⇒ i ⇒ i) ⇒ (i ⇒ i) ⇒ i ⇒ i" (* uses case, split *)
Formula.formula.formula_rec :: "(i ⇒ i ⇒ i) ⇒ (i ⇒ i ⇒ i) ⇒ (i ⇒ i ⇒ i ⇒ i ⇒ i) ⇒ (i ⇒ i ⇒ i) ⇒ i ⇒ i" (* uses Vrecursor, formula_case *)
List.list.list_case :: "i ⇒ (i ⇒ i ⇒ i) ⇒ i ⇒ i" (* uses case, split *)
List.list.list_rec :: "i ⇒ (i ⇒ i ⇒ i ⇒ i) ⇒ i ⇒ i" (* uses Vrecursor, list_case *)
List.map :: "(i ⇒ i) ⇒ i ⇒ i" (* no map_def !!! -- primrec *)
Nat.nat_case :: "i ⇒ (i ⇒ i) ⇒ i ⇒ i" (* uses The -- absolute *)
Nat.nat_rec :: "i ⇒ i ⇒ (i ⇒ i ⇒ i) ⇒ i" (* uses wfrec, nat_case *)
Normal.Closed :: "(i ⇒ o) ⇒ o" (* has abs *)
Normal.Closed_Unbounded :: "(i ⇒ o) ⇒ o"
Normal.Normal :: "(i ⇒ i) ⇒ o"
Normal.Unbounded :: "(i ⇒ o) ⇒ o"
Normal.cont_Ord :: "(i ⇒ i) ⇒ o"
Normal.cub_family :: "(i ⇒ i ⇒ o) ⇒ i ⇒ o"
Normal.mono_Ord :: "(i ⇒ i) ⇒ o"
Normal.mono_le_subset :: "(i ⇒ i) ⇒ o"
Normal.normalize :: "(i ⇒ i) ⇒ i ⇒ i"
OrdQuant.OUnion :: "i ⇒ (i ⇒ i) ⇒ i"
OrdQuant.oall :: "i ⇒ (i ⇒ o) ⇒ o" (* has abs *)
OrdQuant.oex :: "i ⇒ (i ⇒ o) ⇒ o" (* has abs *)
OrderArith.measure :: "i ⇒ (i ⇒ i) ⇒ i" (* has abs *)
QPair.QSigma :: "i ⇒ (i ⇒ i) ⇒ i" 
QPair.qcase :: "(i ⇒ i) ⇒ (i ⇒ i) ⇒ i ⇒ i" (* uses qsplit *)
QPair.qsplit :: "(i ⇒ i ⇒ 'a) ⇒ i ⇒ 'a"
Recursion_Thms.Rrel :: "(i ⇒ i ⇒ o) ⇒ i ⇒ i" (* has abs *)
Reflection.reflection :: "(i ⇒ i) ⇒ o" (* uses mono_le_subset, cont_Ord, Limit *)
Sum.case :: "(i ⇒ i) ⇒ (i ⇒ i) ⇒ i ⇒ i"
Univ.Vrec :: "i ⇒ (i ⇒ i ⇒ i) ⇒ i" (* uses Vfrom, rank *)
Univ.Vrecursor :: "(i ⇒ i ⇒ i) ⇒ i ⇒ i" (* uses Vfrom, rank *)
WF.is_recfun :: "i ⇒ i ⇒ (i ⇒ i ⇒ i) ⇒ i ⇒ o" (* -- low level *)
WF.the_recfun :: "i ⇒ i ⇒ (i ⇒ i ⇒ i) ⇒ i" (* uses The, is_recfun -- low level *)
WF.wfrec :: "i ⇒ i ⇒ (i ⇒ i ⇒ i) ⇒ i" (* uses wftrec *)
WF.wfrec_on :: "i ⇒ i ⇒ i ⇒ (i ⇒ i ⇒ i) ⇒ i" (* uses wfrec *)
WF.wftrec :: "i ⇒ i ⇒ (i ⇒ i ⇒ i) ⇒ i" (* uses the_recfun *)
ZF.iterates :: "(i ⇒ i) ⇒ i ⇒ i ⇒ i"  (* no iterates_def !!! -- primrec *)
ZF.iterates_omega :: "(i ⇒ i) ⇒ i ⇒ i" (* uses iterates *)
ZF.transrec3 :: "i ⇒ i ⇒ (i ⇒ i ⇒ i) ⇒ (i ⇒ i ⇒ i) ⇒ i" (* uses transrec *)
ZF_Base.Ball :: "i ⇒ (i ⇒ o) ⇒ o"
ZF_Base.Bex :: "i ⇒ (i ⇒ o) ⇒ o"
ZF_Base.Collect :: "i ⇒ (i ⇒ o) ⇒ i"
ZF_Base.Lambda :: "i ⇒ (i ⇒ i) ⇒ i"
ZF_Base.Pi :: "i ⇒ (i ⇒ i) ⇒ i"
ZF_Base.PrimReplace :: "i ⇒ (i ⇒ i ⇒ o) ⇒ i" (* low level *)
ZF_Base.RepFun :: "i ⇒ (i ⇒ i) ⇒ i"
ZF_Base.Replace :: "i ⇒ (i ⇒ i ⇒ o) ⇒ i"
ZF_Base.Sigma :: "i ⇒ (i ⇒ i) ⇒ i"
ZF_Base.The :: "(i ⇒ o) ⇒ i"
ZF_Base.split :: "(i ⇒ i ⇒ 'a) ⇒ i ⇒ 'a"
