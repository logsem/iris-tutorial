BEGIN {
    in_solution = 0; # for the advanced solution syntax
    in_auto_solution = 0; # for the simple solution syntax that recognizes `Qed.`
}
{ # on every line of the input
    if (match($0, /^( *)\(\* *SOLUTION *\*\) *Proof.$/, groups)) {
        print groups[1] "Proof."
        in_auto_solution = 1
    } else if (in_auto_solution == 1 && match($0, /^( *)Qed.$/, groups)) {
        print groups[1] "  (* exercise *)"
        print groups[1] "Admitted."
        in_auto_solution = 0
    } else if (match($0, /^( *)\(\* *BEGIN SOLUTION *\*\)$/, groups)) {
        in_solution = 1
    } else if (match($0, /^( *)\(\* *END SOLUTION BEGIN TEMPLATE *$/, groups)) {
        in_solution = 0
    } else if (match($0, /^( *)END TEMPLATE *\*\)$/, groups)) {
        # Nothing to do, just do not print this line.
    } else if (in_solution == 0 && in_auto_solution == 0) {
        gsub("From solutions Require", "From exercises Require")
        print
    }
}
