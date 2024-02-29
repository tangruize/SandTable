#!/bin/bash

# To automatically exit tmux when all servers are closed
#TMUX_AUTO_EXIT=true
TMUX_AUTO_EXIT=${TMUX_AUTO_EXIT:-false}

# Not to attach to tmux session
#TMUX_DETACH=true
TMUX_DETACH=${TMUX_DETACH:-false}

#DEFAULT_TERM=tmux
#DEFAULT_TERM=gnome-terminal
DEFAULT_TERM=$DEFAULT_TERM

# Run tmux in client SSH (client must have "tmux" installed!)
#CLIENT_TMUX=true
CLIENT_TMUX=${CLIENT_TMUX:-false}

# Send stty cmd if window size changed
#AUTO_RESIZE=true
AUTO_RESIZE=${AUTO_RESIZE:-false}

# GUI terminal geometries
#GEOMETRIES=(80x24 110x28 ..)
GEOMETRIES=(${GEOMETRY[@]})

# Not to allocate tty, use "script" to create a fake tty (client must have "script" installed!)
#FAKE_TTY=true
FAKE_TTY=${FAKE_TTY:-false}

# Not to allocate tty (fast for sending files), it defines a "_start" function to allocate a fake tty
#NO_TTY=true
NO_TTY=${NO_TTY:-false}

# If stdin is not tty, set NO_TTY=true
#NO_TTY_IF_PIPED=true
NO_TTY_IF_PIPED=${NO_TTY_IF_PIPED:-false}

if test -z "$DISPLAY" -a -z "$DEFAULT_TERM"; then
    DEFAULT_TERM=tmux
fi

terms=($DEFAULT_TERM x-terminal-emulator gnome-terminal konsole mate-terminal xfce4-terminal tmux)
if [ -z "$XTERM" ]; then
    for t in ${terms[*]}; do
        if [ $(command -v $t) ]; then
            export XTERM=$t
            break
        fi
    done
fi

REPL_KILL_WHEN_EXIT="--kill-when-exit"
REPL_PIPE="--pipe"

function repl {
    local timeout=$2
    if [ -n "$timeout" ]; then
        TIMEOUT_CMD="timeout --foreground $timeout"
    fi
    if [ "$1" = "$REPL_PIPE" ]; then
        if [ -z "$SESSION" ]; then
            if [ -d "$TMPDIR" ]; then
                SESSION=SSH$(echo -n "${TMPDIR%.spssh}" | tail -c4)
            else
                test -t 0 && read -p "Enter last four chars of tmux SESSION (press ENTER if backend is not tmux): " SESSION
                SESSION=${SESSION:+SSH${SESSION#SSH}}
            fi
        fi
        if [ -n "$SESSION" -a -t 0 ]; then
            if tmux select-window -t "$SESSION:0" 1>&2; then
                tmux select-pane -t "$SESSION:0.0"
                exec tmux attach-session -d -t "$SESSION" 1>&2
            fi
        fi
    else
        if [ "$1" = "$REPL_KILL_WHEN_EXIT" ]; then
            IS_KILL=true
        fi
        TMPFILE=$TMPDIR/host
        SEQFILE=$TMPDIR/seq
        NO_PIPE_ARG='> /dev/null'
    fi
    if [ -n "$TMPFILE" -a -z "$TMPDIR" ]; then
        echo "Error: TMPDIR is not set" 1>&2
        exit 1
    fi
    if test -t 0; then
        HISTORY=$(mktemp --suffix=.history)
        echo -n "Run commands on all servers" 1>&2
        if test "$IS_KILL" = true -o "$1" = "$REPL_PIPE"; then
            echo ", Ctrl + D to exit all servers, Ctrl + \\ to switch line/char mode:" 1>&2
        else
            echo ", Ctrl + D to exit current repl, Ctrl + \\ to switch line/char mode:" 1>&2
        fi
        EXIT_CMD="rm -f $HISTORY; test '$IS_KILL' = true && rm -f $TMPFILE $SEQFILE 2>/dev/null; test -d $TMPDIR && rmdir --ignore-fail-on-non-empty $TMPDIR 2> /dev/null"
        trap "$EXIT_CMD" EXIT
        stty intr undef
        bash -c "resize() { if test -n \"\$TMUX\"; then W=\$(tput cols); H=\$(tput lines); echo \" test -z \\\$TMUX && stty cols \$W rows \$H 2>/dev/null\"; fi }; cmr() { read -rN 1 r; }; cme() { echo -n \"\$r\"; }; lmr() { read -rep '$ ' r; }; lme() { if test \"\$s\" = 1; then true; elif test \"\$r\" = '#RESIZE'; then resize; else echo \"\$r\"; fi; }; run_repl() { m=l; trap 'echo 1>&2; echo 1>&2 -n Presss ENTER to switch to\ ; if test \$m = l; then m=c; echo 1>&2 char mode; else m=l; s=1; echo 1>&2 line mode; fi' QUIT; HISTFILE=$HISTORY; set -o history;  while eval \\\${m}mr; do eval \\\${m}me | tee -a $TMPFILE $HISTORY $NO_PIPE_ARG; history -n; unset s; done; set +o history; }; export -f resize cmr cme lmr lme run_repl; exec $TIMEOUT_CMD bash -c 'run_repl'"
        eval "$EXIT_CMD"
        trap EXIT
        if test "$IS_KILL" = "true"; then
            find $TMPDIR -type p -exec lsof -t {} + 2>/dev/null | xargs --no-run-if-empty kill
        fi
        stty intr ^C
    else
        trap '' QUIT
        if test "$1" = "$REPL_PIPE"; then
            cat
        else
            cat >> "$TMPFILE"
        fi
        trap QUIT
    fi
    if [ "$1" = "$REPL_PIPE" ]; then
        exit 1
    fi
}

function usage() {
    cat <<EOF
spssh.sh [--tmux [--detach --auto-exit --run-host-cmd --save-output --wait-for 
          --join-windows --no-change-prefix-with-client-tmux 'host cmd']]
         [--gnome/mate/xfce4-terminal --konsole [--geometry 80x24+0+0 ..]]
         [--client-tmux] [--auto-resize] [--force-bash] [--quiet] [--compress] 
         [--fake-tty] [--no-tty] [--no-tty-if-piped] [--no-host-key-checking]
         [--timeout] [--simple-tmp-filename] 'user1@server1 [SSH_ARGS ..]' ..
spssh.sh [-t [-d -e -r 'cmd' -s -w -j -n]]/[-g/-m/-x/-k [-G 'geometry' ..]]
         [-c] [-a] [-b] [-q] [-C] [-F/-N/-P] [-H] [-T] [-S]
         'user1@server1 [SSH_ARGS ..]' ..
spssh.sh --repl [$REPL_KILL_WHEN_EXIT]  # in tmux session
EOF
}

while test "$#" -gt 0; do
    case "$1" in
        -g|--gnome-terminal)
            export XTERM=gnome-terminal
            ;;
        -k|--konsole)
            export XTERM=konsole
            ;;
        -m|--mate-terminal)
            export XTERM=mate-terminal
            ;;
        -x|--xfce4-terminal)
            export XTERM=xfce4-terminal
            ;;
        -t|--tmux)
            export XTERM=tmux
            while test -n "$2"; do
                case "$2" in
                    -d|--detach)
                        TMUX_DETACH=true
                        shift
                        ;;
                    -e|--auto-exit)
                        TMUX_AUTO_EXIT=true
                        shift
                        ;;
                    -r|--run-host-cmd)
                        TMUX_RUN_HOST_CMD="$3"
                        shift 2
                        ;;
                    -n|--no-change-prefix-with-client-tmux)
                        TMUX_NO_CHANGE_PREFIX=true
                        shift
                        ;;
                    -s|--save-output)
                        TMUX_SAVE_OUTPUT=true
                        shift
                        ;;
                    -w|--wait-for)
                        TMUX_WAIT_FOR_S="$3"
                        TMUX_WAIT_FOR_CMD="tmux wait-for -S '$TMUX_WAIT_FOR_S'"
                        shift 2
                        ;;
                    -j|--join-windows)
                        TMUX_JOIN_WINDOWS=true
                        shift
                        ;;
                    *)
                        break
                        ;;
                esac
            done
            ;;
        -c|--client-tmux)
            CLIENT_TMUX=true
            ;;
        -a|--auto-resize)
            AUTO_RESIZE=true
            ;;
        -b|--force-bash)
            FORCE_BASH=true
            ;;
        -q|--quiet)
            QUIET=true
            ;;
        -P|--no-tty-if-piped)
            NO_TTY_IF_PIPED=true
            ;;
        -G|--geometry)
            GEOMETRIES=(${GEOMETRIES[@]} $2)
            shift
            ;;
        -R|--repl)
            if test "$2"; then
                if test "$2" != "$REPL_KILL_WHEN_EXIT" -a "$2" != "$REPL_PIPE"; then
                    usage
                    exit 2
                fi
            fi
            repl $2 $TIMEOUT
            exit
            ;;
        -C|--compress)
            SSH_ARGS+=' -C'
            ;;
        -F|--fake-tty)
            # seems useless
            FAKE_TTY=true
            ;;
        -N|--no-tty)
            # very fast for sending files, combined with spssh_cp.sh --fake-tty
            NO_TTY=true
            ;;
        -S|--simple-tmp-filename)
            SIMPLE_TMP_FN=true
            ;;
        -H|--no-host-key-checking)
            SSH_ARGS+=' -o StrictHostKeyChecking=no -o UserKnownHostsFile=/dev/null -o LogLevel=ERROR'
            ;;
        -T|--timeout)
            TIMEOUT=$2
            TIMEOUT_ARG="-T $TIMEOUT"
            shift
            ;;
        -*)
            usage
            exit 1
            ;;
        *)
            break
            ;;
    esac
    HAS_ARG=true
    shift
done

if test "$#" -eq 0 && (test -z "$HAS_ARG" || test "$XTERM" != "tmux"); then
    usage
    exit 1
elif [ -z "$(command -v $XTERM)" ]; then
    echo Error: Cannot find a terminal emulator
    exit 2
fi

if test "$NO_TTY_IF_PIPED" = "true" -a ! -t 0; then
    NO_TTY=true
fi

if test "$NO_TTY" = "true"; then
    FAKE_TTY=true
fi

if test "$FAKE_TTY" = "true"; then
    SSH_ARGS+=' -T'
else
    SSH_ARGS+=' -tt'
fi

if test "$CLIENT_TMUX" = "true"; then
    AUTO_RESIZE=false
    TMUX_JOIN_WINDOWS=false
fi

set -e
if test -z "$TMPDIR"; then
    TMPDIR=$(mktemp -d -p /tmp --suffix=.spssh)
    export TMPDIR
    test "$QUIET" != true && echo "[SPSSH] TMPDIR=$TMPDIR" 1>&2
elif test -f "$TMPDIR/host"; then
    ALREADY_RUNNING=true
else
    mkdir -p "$TMPDIR"
fi
set +e
TMPFILE=$TMPDIR/host
SEQFILE=$TMPDIR/seq
touch "$TMPFILE" "$SEQFILE"
RMTMPDIR="rmdir --ignore-fail-on-non-empty $TMPDIR 2> /dev/null"

if test -z "$ALREADY_RUNNING"; then
    trap "echo Quitting ...; trap '' INT TERM" INT TERM
    if test "$XTERM" != "tmux"; then
        trap "sleep 1; rm -f $TMPFILE $SEQFILE 2>/dev/null; $RMTMPDIR" EXIT
    fi
fi

if test -z "$SESSION"; then
    export SESSION=SSH$(echo -n "${TMPDIR%.spssh}" | tail -c4)
fi

if test "$FORCE_BASH" = "true"; then
    EXPORT_SHELL_CMD="export SHELL=/bin/bash; "
    TMUX_HOST_SHELL="/bin/bash"
fi

if [ "$XTERM" = "tmux" ]; then
    if test -z "$ALREADY_RUNNING"; then
        test "$QUIET" != true && echo "[SPSSH] SESSION=$SESSION" 1>&2
        export WIDTH=$(tput cols || echo 80)
        export HEIGHT=$(($(tput lines || echo 24)-1))
        set -e
        if ! tmux has-session -t "$SESSION" 2>/dev/null; then
            if test "$CLIENT_TMUX" = "true"; then
                TMUX_MOUSE_OPTION="tmux set-option mouse off;"
                if test "$TMUX_NO_CHANGE_PREFIX" != "true"; then
                    TMUX_CHANGE_PREFIX="tmux set-option prefix C-a; tmux bind C-a send-prefix;"
                fi
            fi
            tmux new-session -d -s "$SESSION" -n "HOST" -x "$WIDTH" -y "$HEIGHT" -e "TMUX_AUTO_EXIT=$TMUX_AUTO_EXIT" -e "DEFAULT_TERM=$DEFAULT_TERM" -e "CLIENT_TMUX=$CLIENT_TMUX" -e "TMPDIR=$TMPDIR" -e "DISPLAY=$DISPLAY" -e "SESSION=$SESSION" -e "WIDTH=$WIDTH" -e "HEIGHT=$HEIGHT" "bash -c 'set -x; $TMUX_MOUSE_OPTION $TMUX_CHANGE_PREFIX'; $0 $TIMEOUT_ARG --repl $REPL_KILL_WHEN_EXIT; $TMUX_WAIT_FOR_CMD"
        elif test -n "$TMUX"; then
            CURRENT_IN_TMUX=true
        else
            tmux split-window -t "$SESSION:0" "exec $0 $TIMEOUT_ARG --repl $REPL_KILL_WHEN_EXIT"
        fi
        set +e
    fi
    if test "$TMUX_AUTO_EXIT" != "false"; then
        KILLHOST="tmux kill-pane -t $SESSION:0.0"
    fi
    if test "$TMUX_RUN_HOST_CMD"; then
        tmux split-window -t "$SESSION:0" $TMUX_HOST_SHELL
        if test -n "$TMUX_SAVE_OUTPUT"; then
            TMUX_SAVE_CMD='trap "tmux capture-pane -pJS - -t $TMUX_PANE > log.host" EXIT'
            tmux send-keys -t "$SESSION:0" "$TMUX_SAVE_CMD" C-m
            if test "$KILLHOST"; then
                KILLHOST="sleep 0.1; $KILLHOST"
            fi
        fi
        tmux send-keys -t "$SESSION:0" "$TMUX_RUN_HOST_CMD" C-l C-m
    fi
    STTY_CMD=" stty cols $WIDTH rows $HEIGHT 2>/dev/null;"
else
    KILLHOST="kill -INT -- -$$"
fi

function set_geometry() {
    if [ "$XTERM" = "tmux" ]; then
        return
    fi
    unset GEOMETRY_OPTIONS
    if test "$CLIENT_TMUX" = 'true'; then
        DEFAULT_HEIGHT=25
    else
        DEFAULT_HEIGHT=24
    fi
    GEOMETRY=${GEOMETRIES[0]:-80x$DEFAULT_HEIGHT}
    if [ "${#GEOMETRIES[@]}" -gt 1 ]; then
        unset GEOMETRIES[0]
        GEOMETRIES=(${GEOMETRIES[@]})
    fi
    XSIZE=($(tr '[+x\-]' ' ' <<< "$GEOMETRY"))
    WIDTH=${XSIZE[0]:-80}
    HEIGHT=${XSIZE[1]:-$DEFAULT_HEIGHT}
    if [ "$XTERM" = "konsole" ]; then
        # konsole (v22.04.1) may increase/decrease the row by 1...
        if [ -n "${XSIZE[2]}" -a -n "${XSIZE[3]}" ]; then
            GEOMETRY_OPTIONS="--geometry $(sed -E 's/[0-9]+x[0-9]+(.*)/\1/' <<< "$GEOMETRY")"
        fi
    fi
    STTY_CMD=" stty cols $WIDTH rows $HEIGHT 2>/dev/null;"
}

function set_ssh_cmd() {
    SSH_START_CMD=
    SSH_NO=$1
    if [ "$CLIENT_TMUX" = true ]; then
        SSH_NAME_PREFIX=SSH$(echo -n ${SESSION#SSH} | head -c 2)
        SSH_NAME=$SSH_NAME_PREFIX$(echo -n $(mktemp -u) | tail -c 2)
        TMUX_CLIENT_ENV="-x $WIDTH -y $((HEIGHT-1)) -e SSH_NO=$SSH_NO -e DISPLAY=\\\${DISPLAY:- }"
        if [ "$NO_TTY" != "true" ]; then
            # too many escapes (cannot esape quotes any more) !!
            TMUX_CLIENT_ENV="$TMUX_CLIENT_ENV -e SSH_CLIENT=\\\"\\\$SSH_CLIENT\\\" -e SSH_CONNECTION=\\\"\\\$SSH_CONNECTION\\\" -e SSH_TTY=\\\"\\\$SSH_TTY\\\""
        fi
        SSH_START_CMD="$STTY_CMD export SHELL=\\\$SHELL; $EXPORT_SHELL_CMD if tmux new-session -d -t $SSH_NAME_PREFIX -s $SSH_NAME_PREFIX $TMUX_CLIENT_ENV 2>/dev/null; then tmux set-option -t $SSH_NAME_PREFIX mouse on; exec tmux attach-session -t $SSH_NAME_PREFIX; else tmux new-session -d -t $SSH_NAME_PREFIX -s $SSH_NAME $TMUX_CLIENT_ENV; tmux new-window -t $SSH_NAME; tmux set-option -t $SSH_NAME mouse on; exec tmux attach-session -t $SSH_NAME; fi"
    fi

    SSH_START_CMD="${SSH_START_CMD:-$STTY_CMD export SSH_NO=$SSH_NO; $EXPORT_SHELL_CMD exec \\\$SHELL}"

    if [ "$FAKE_TTY" = "true" ]; then
        SSH_START_CMD="export TERM=xterm-256color; exec script -qc \\\"${SSH_START_CMD//\\/\\\\\\}\\\" /dev/null"
    fi

    if [ "$NO_TTY" = "true" ]; then
        SSH_START_CMD="bash -c \\\"function _start() { ${SSH_START_CMD//\\/\\\\\\}; }; export -f _start; export SSH_NO=$SSH_NO; exec bash\\\""
    fi
}

KILLCAT="pkill -g 0 -x cat; pkill -g 0 -x python3"
KILLEXIT="find $TMPDIR -type p -exec false {} + 2>/dev/null && ($RMTMPDIR; $KILLHOST)"

function set_cat() {
    FIFO_FILE=$1
    if [ -n "$(command -v python3)" -a -n "$(command -v base64)" -a "$AUTO_RESIZE" = "true" ]; then
        PYTHON_AUTO_RESIZE_CAT=$(cat <<EOF
import os
import sys
import signal
o = os.open(sys.argv[1], os.O_APPEND|os.O_WRONLY)
def winch_handler(sig, frame):
    x,y = os.get_terminal_size()
    os.write(o, b' test -z \$TMUX && stty rows ' + str(y).encode() + b' cols ' + str(x).encode() + b' 2>/dev/null\n')
signal.signal(signal.SIGWINCH, winch_handler)
while True:
    i = os.read(0, 4096)
    if len(i) <= 0:
        os.close(o)
        quit()
    os.write(o, i)
EOF
    )
        CAT_PROGRAM="python3 -c \"\$(echo $(base64 -w 0 <<< "$PYTHON_AUTO_RESIZE_CAT") | base64 -d)\" $FIFO_FILE"
    else
        CAT_PROGRAM="cat >> $FIFO_FILE"
    fi
}

while test "$#" -gt 0; do
    if test "$SIMPLE_TMP_FN" = true; then
        TMPFIFO="$TMPDIR/ssh"
    else
        TMPFIFO=$(mktemp -u --suffix=.ssh)
    fi
    SEQ=$(cat $SEQFILE)
    SEQ=$((SEQ+1))
    echo $SEQ > "$SEQFILE"
    TMPFIFO=${TMPFIFO}.$((SEQ))
    mkfifo $TMPFIFO
    set_geometry
    set_ssh_cmd $SEQ
    set_cat $TMPFIFO
    CMD="bash -c 'run_ssh() { trap \"rm -f $TMPFIFO; $KILLEXIT\" EXIT; stty -echo -echoctl raw; (tail -n +1 -F $TMPFILE >> $TMPFIFO 2>/dev/null; $KILLCAT) & (setsid ssh $SSH_ARGS $1 \"$SSH_START_CMD\" < $TMPFIFO; $KILLCAT) & $CAT_PROGRAM; }; export -f run_ssh; exec bash -c \"run_ssh\"'"
    if test -n "$ALREADY_RUNNING"; then
        truncate -cs 0 "$TMPFILE"
    fi
    if test -n "$TMUX_SAVE_OUTPUT"; then
        TMUX_SAVE_CMD="; tmux capture-pane -pJS - -t \$TMUX_PANE > log.$SEQ"
    fi
    NAME=$(echo "$1" | grep -o '[^ ]*@[^ ]*' | head -1 | tr '.' '_')_${TMPFIFO##*.}
    case "$XTERM" in
        tmux)
            tmux new-window -d -t "$SESSION" -n "$NAME" "$CMD$TMUX_SAVE_CMD"
            ;;
        gnome-terminal)
            eval $XTERM --geometry="$GEOMETRY" --title="$NAME" -- $CMD & sleep 0.1
            ;;
        konsole)
            $XTERM -p "tabtitle=$NAME" -p "TerminalColumns=$WIDTH" -p "TerminalRows=$HEIGHT" $GEOMETRY_OPTIONS -e "$CMD" & sleep 0.1
            ;;
        *)
            $XTERM --geometry="$GEOMETRY" --title="$NAME" -e "$CMD" & sleep 0.1
            ;;
    esac
    shift
done

if test -z "$ALREADY_RUNNING"; then
    if test "$TMUX_JOIN_WINDOWS" = true; then
        for ((s=$SEQ;s>0;s--)); do
            tmux join-pane -d -s @$s -t $SESSION:0${TMUX_RUN_HOST_CMD:+.1}
        done
        tmux select-layout even-vertical
    fi
    if test "$XTERM" = "tmux" -a "$CURRENT_IN_TMUX" != "true"; then
        tmux select-window -t "$SESSION:0"
        tmux select-pane -t "$SESSION:0.0"
    fi
    if test -t 0 -a "$XTERM" = "tmux" -a "$CURRENT_IN_TMUX" != "true"; then
        if test "$TMUX_DETACH" != "true"; then
            if test "$QUIET" = true; then
                exec tmux attach-session -d -t "$SESSION" >/dev/null
            else
                exec tmux attach-session -d -t "$SESSION"
            fi
        fi
    else
        repl $REPL_KILL_WHEN_EXIT $TIMEOUT
    fi
elif ! test -t 0; then
    repl "" $TIMEOUT
fi
