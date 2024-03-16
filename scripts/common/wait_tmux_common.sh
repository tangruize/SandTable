if test -t 0; then
    tmux attach -t SSH$(echo -n $TMPDIR | tail -c 4)>/dev/null
else
    tmux wait-for "$TMPDIR"
fi