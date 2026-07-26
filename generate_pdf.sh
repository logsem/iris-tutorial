#!/usr/bin/env bash
set -euo pipefail

HTML_DIR="html"
TOC_FILE="${HTML_DIR}/toc.html"

if [ ! -f "$TOC_FILE" ]; then
    echo "Error: $TOC_FILE not found! Run 'make html' first."
    exit 1
fi

generate_for() {
    local PREFIX=$1
    local FILTERED_TOC="${HTML_DIR}/toc_${PREFIX}.html"
    local OUTPUT_PDF="${PREFIX}.pdf"

    # Capitalize the first letter for the title (Bash 4.0+)
    local TITLE="Iris Tutorial - ${PREFIX^}"

    echo "--- Building ${OUTPUT_PDF} ---"

    # 1. Generate the filtered TOC
    # This awk script passes through everything outside `<div id="toc">`.
    # Inside the TOC, it checks each `<h2>` to see if the link belongs to
    # the current prefix (e.g., "solutions"). If so, it keeps printing until
    # the next `<h2>` tells it to stop.
    awk -v prefix="$PREFIX" '
    BEGIN { printing = 1; in_toc = 0; }
    /<div id="toc">/ { in_toc = 1; print; next; }
    /<\/div>/ && in_toc { in_toc = 0; print; next; }
    /<h2/ && in_toc {
        if ($0 ~ "href=\"" prefix "\\.") printing = 1;
        else printing = 0;
    }
    { if (!in_toc || printing) print; }
    ' "$TOC_FILE" > "$FILTERED_TOC"

    # 2. Extract the ordered list of HTML filenames for this prefix.
    # By only looking at lines with '<h2', we cleanly grab the top-level files.
    local FILES
    FILES=$(grep '<h2' "$TOC_FILE" | grep -oE 'href="'"${PREFIX}"'\.[^"]*\.html"' | cut -d'"' -f2 | awk '!x[$0]++')

    # 3. Assemble inputs (starting with the filtered TOC)
    local INPUTS=("$FILTERED_TOC")
    for f in $FILES; do
        INPUTS+=("${HTML_DIR}/$f")
    done

    echo "Combining ${#INPUTS[@]} HTML files into ${OUTPUT_PDF}..."

    # 4. Generate the PDF
    wkhtmltopdf \
        --enable-local-file-access \
        --javascript-delay 500 \
        --title "$TITLE" \
        --footer-center "[page] / [topage]" \
        "${INPUTS[@]}" \
        "$OUTPUT_PDF"

    echo "+++ Successfully generated ${OUTPUT_PDF} +++"
    echo ""
}

generate_for "exercises"
generate_for "solutions"
