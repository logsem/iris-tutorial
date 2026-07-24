BEGIN {
    in_solution = 0; # for the advanced solution syntax
    in_auto_solution = 0; # for the simple solution syntax that recognizes `Qed.`
}
{ # on every line of the input
    # Capture leading whitespace into 's' to replace groups[1]
    match($0, /^[ ]*/)
    s = substr($0, 1, RLENGTH)

    if ($0 ~ /^[ ]*\(\* *SOLUTION *\*\) *Proof.$/) {
        print s "Proof."
        in_auto_solution = 1
    } else if (in_auto_solution == 1 && $0 ~ /^[ ]*Qed.$/) {
        print s "  (* exercise *)"
        print s "Admitted."
        in_auto_solution = 0
    } else if ($0 ~ /^[ ]*\(\* *BEGIN SOLUTION *\*\)$/) {
        in_solution = 1
    } else if ($0 ~ /^[ ]*\(\* *END SOLUTION BEGIN TEMPLATE/) {
        in_solution = 0
    } else if ($0 ~ /^[ ]*END TEMPLATE *\*\)$/) {
        # Nothing to do, just do not print this line.
    } else if (in_solution == 0 && in_auto_solution == 0) {
        gsub("From solutions Require", "From exercises Require")
        print
    }
}
