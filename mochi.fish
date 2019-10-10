#!/usr/bin/env fish

# options
complete -c mochi -a "(mochi -option-list)"

# for "-debug" option
complete -c mochi -o debug -x -a "(mochi -debug-list)"

# for "-trans" option
complete -c mochi -o trans -x -a "(mochi -trans-list)"

# files
complete -c mochi -x -a "(
__fish_complete_suffix .ml
__fish_complete_suffix .cegar
)"
