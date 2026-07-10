rm Q0_completeness.zip

mkdir Q0_completeness
cp Consistency_Property.thy Q0_completeness
cp Constant_Substitution.thy Q0_completeness
cp Derivational_Consistency.thy Q0_completeness
cp Model_Existence.thy Q0_completeness
cp Q0_Completeness.thy Q0_completeness
cp README_submission.txt Q0_completeness/README.txt
cp ROOT_submission Q0_completeness/ROOT

zip -rXq Q0_completeness.zip Q0_completeness

rm -r Q0_completeness

