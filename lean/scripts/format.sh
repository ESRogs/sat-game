#!/bin/bash
# Fix trailing whitespace, ensure newline endings, and order imports in all .lean files

set -e

echo "🔍 Checking .lean files for formatting issues..."

fixed_whitespace=false
fixed_newlines=false
fixed_imports=false

# Function to order imports in a file
order_imports() {
    local file="$1"
    local tempfile=$(mktemp)
    trap 'rm -f "$tempfile"' EXIT

    # Extract the import section (continuous imports from the start)
    local in_imports=true
    local import_section=""
    local trailing_newlines=""
    local rest_of_file=""

    while IFS= read -r line; do
        if [[ "$in_imports" == true ]]; then
            if [[ "$line" =~ ^import[[:space:]] ]]; then
                import_section="${import_section}${line}"$'\n'
                trailing_newlines=""  # Reset trailing newlines when we see an import
            elif [[ -z "$line" || "$line" =~ ^[[:space:]]*$ ]]; then
                # Empty line, accumulate as trailing newlines
                trailing_newlines="${trailing_newlines}"$'\n'
            else
                # First non-import, non-empty line
                in_imports=false
                rest_of_file="${line}"$'\n'
            fi
        else
            rest_of_file="${rest_of_file}${line}"$'\n'
        fi
    done < "$file"

    # If no imports found, return
    if [[ ! "$import_section" =~ import ]]; then
        return 0
    fi

    # Sort imports into groups
    local batteries_imports=""
    local mathlib_imports=""
    local satgame_imports=""
    local other_imports=""

    while IFS= read -r line; do
        if [[ "$line" =~ ^import[[:space:]] ]]; then
            if [[ "$line" =~ ^import[[:space:]]+Batteries ]]; then
                batteries_imports="${batteries_imports}${line}"$'\n'
            elif [[ "$line" =~ ^import[[:space:]]+Mathlib ]]; then
                mathlib_imports="${mathlib_imports}${line}"$'\n'
            elif [[ "$line" =~ ^import[[:space:]]+SATGame ]]; then
                satgame_imports="${satgame_imports}${line}"$'\n'
            elif [[ ! -z "$line" ]]; then
                other_imports="${other_imports}${line}"$'\n'
            fi
        fi
    done <<< "$import_section"

    # Sort each group
    if [[ -n "$batteries_imports" ]]; then
        batteries_imports=$(echo -n "$batteries_imports" | sort)$'\n'
    fi
    if [[ -n "$mathlib_imports" ]]; then
        mathlib_imports=$(echo -n "$mathlib_imports" | sort)$'\n'
    fi
    if [[ -n "$satgame_imports" ]]; then
        satgame_imports=$(echo -n "$satgame_imports" | sort)$'\n'
    fi
    if [[ -n "$other_imports" ]]; then
        other_imports=$(echo -n "$other_imports" | sort)$'\n'
    fi

    # Reconstruct file with ordered imports
    {
        [[ -n "$batteries_imports" ]] && echo -n "$batteries_imports"
        [[ -n "$mathlib_imports" ]] && echo -n "$mathlib_imports"
        [[ -n "$other_imports" ]] && echo -n "$other_imports"
        [[ -n "$satgame_imports" ]] && echo -n "$satgame_imports"
        echo -n "$trailing_newlines"
        echo -n "$rest_of_file"
    } > "$tempfile"

    # Check if imports were reordered
    if ! cmp -s "$file" "$tempfile"; then
        cp "$tempfile" "$file"
        return 1  # Indicates changes were made
    else
        return 0  # No changes
    fi
}

# Check and fix import ordering
while IFS= read -r -d '' file; do
    if order_imports "$file"; then
        :  # No changes
    else
        echo "❌ File $file had imports reordered"
        fixed_imports=true
    fi
done < <(find . -name "*.lean" -type f ! -path "./.lake/*" -print0)

# Check and fix trailing whitespace
if grep -r '[[:space:]]$' --include="*.lean" . | grep -v '^\./.lake/' > /dev/null 2>&1; then
    echo "❌ Found trailing whitespace, fixing..."
    # Cross-platform sed: macOS requires -i '', Linux requires -i
    if [[ "$OSTYPE" == "darwin"* ]]; then
        find . -name "*.lean" -type f ! -path "./.lake/*" -exec sed -i '' 's/[[:space:]]*$//' {} +
    else
        find . -name "*.lean" -type f ! -path "./.lake/*" -exec sed -i 's/[[:space:]]*$//' {} +
    fi
    fixed_whitespace=true
fi

# Check and fix missing newlines at end of files
while IFS= read -r -d '' file; do
    if [[ -s "$file" ]] && [[ "$(tail -c 1 "$file")" != "" ]]; then
        echo "❌ File $file missing final newline, fixing..."
        echo "" >> "$file"
        fixed_newlines=true
    fi
done < <(find . -name "*.lean" -type f ! -path "./.lake/*" -print0)

# Summary
if [[ "$fixed_whitespace" == true ]] || [[ "$fixed_newlines" == true ]] || [[ "$fixed_imports" == true ]]; then
    echo "✅ Fixed formatting issues in .lean files!"
else
    echo "✅ All .lean files are properly formatted!"
fi
