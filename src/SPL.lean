-- SPL.lean
-- Software Product Line variability
import data.fintype
import data.finset

namespace SPL

variables {Feature : Type}
variables [d : decidable_eq Feature]
variables [t : fintype Feature] 

def Config : Type := finset Feature

instance Config_has_mem : has_mem Feature Config := finset.has_mem

structure SPL :=
    (features : finset Feature)
    (allFeatures : finset Feature := fintype.elems Feature)
    (allConfigs : finset Config := allFeatures.powerset)

end SPL