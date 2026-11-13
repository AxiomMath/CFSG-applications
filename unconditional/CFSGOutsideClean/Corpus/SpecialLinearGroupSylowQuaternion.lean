import CFSG.ClassicalInvolution.QuaternionStructure
import CFSGOutside.Corpus.SpecialLinearGroupSylowQuaternion

/-! The corpus proves the statement that `CFSGOutside.Corpus.SpecialLinearGroupSylowQuaternion` assumes. -/

universe u

instance CFSGOutsideClean.Corpus.specialLinearGroupSylowQuaternion :
    CFSGOutside.Corpus.SpecialLinearGroupSylowQuaternion.{u} :=
  ⟨fun F _ _ hF P => CFSG.ClassicalInvolution.specialLinearGroup_sylow_quaternion F hF P⟩
