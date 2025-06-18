#!/bin/bash
# Fix trailing whitespace and ensure newline endings in all .lean files

set -e

echo "🔍 Checking .lean files for formatting issues..."

fixed_whitespace=false
fixed_newlines=false

# Check and fix trailing whitespace
if grep -r '[[:space:]]$' --include="*.lean" . | grep -v '^\./.lake/' > /dev/null 2>&1; then
    echo "❌ Found trailing whitespace, fixing..."
    find . -name "*.lean" -type f ! -path "./.lake/*" -exec sed -i '' 's/[[:space:]]*$//' {} +
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
if [[ "$fixed_whitespace" == true ]] || [[ "$fixed_newlines" == true ]]; then
    echo "✅ Fixed formatting issues in .lean files!"
else
    echo "✅ All .lean files are properly formatted!"
fi
