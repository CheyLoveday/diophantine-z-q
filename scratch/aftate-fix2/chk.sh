#!/bin/bash
# usage: chk.sh file.lean  -> writes file.out, prints errors (one Lean process)
cd ~/dzq-wt/aftate-fix2
export PATH="$HOME/bin:$HOME/.elan/bin:$PATH"
uptime; free -g | sed -n 2p
f=$1; o=${f%.lean}.out
start=$(date +%s)
timeout 1500 lake env lean "$f" > "$o" 2>&1
echo "EXIT $? after $(( $(date +%s) - start ))s" >> "$o"
grep -v "linter\|^Note\|^consider\|^  omit" "$o" | grep -B1 -A18 "error" | head -${2:-200}
tail -1 "$o"
