# KNOWNTARGETS will not be passed along to RocqMakefile
KNOWNTARGETS := RocqMakefile
# KNOWNFILES will not get implicit targets from the final rule, and so depending on them won’t invoke the submake
# Warning: These files get declared as PHONY, so any targets depending on them always get rebuilt
KNOWNFILES := Makefile _RocqProject

.DEFAULT_GOAL := invoke-rocqmakefile

RocqMakefile: Makefile _RocqProject
	$(ROCQBIN)rocq makefile -f _RocqProject -o RocqMakefile

invoke-rocqmakefile: RocqMakefile
	$(MAKE) --no-print-directory -f RocqMakefile $(filter-out $(KNOWNTARGETS),$(MAKECMDGOALS))

.PHONY: invoke-rocqmakefile $(KNOWNFILES)

# This should be the last rule, to handle any targets not declared above
%: invoke-rocqmakefile
	@true
