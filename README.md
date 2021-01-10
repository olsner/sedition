sedition
========

This is a dialect of sed, extended with some useful features:

* Networking (currently: listening and accepting TCP connections)
* Threading - implemented as a (f)ork command that takes a block or command to
  run in a new thread
* Inter-thread communications
* Extended hold space, a key/value store extending the normal single hold space
* Built-in optimizer and (eventually) compiler

Some GNU sed features have been included, and the regular expressions are
always the extended variety (as if the -r flag was passed to sed). There may
be other subtle differences in regexp dialect between sed and the regex-tdfa
package used though.

## Building and Getting Started

* Install ghc (>= 8.0.2 for a working version of hoopl) and cabal-install, make
  sure they're in your PATH.
* Install Haskell prerequisites: `./boot.sh`
* Build with `make`

The produced sed executable accepts the usual sed command-line options. (But
not all of them.)

## Examples

* A simple echo server:

        0 L1 :7
        :egin
        # Allow this code to run on line 0 (before-first-line)
        0{
            A 1 2
            # Fork: setup: redirect 2 to 0, then loop doing nothing (= cat)
            f 0 < 0 2
            # In main, close 2
            < 2
            # Loop without waiting for a line on stdin
            begin
        }


## Added addresses

* `0` - Pre-first line

    Since normal sed only starts running code on the first line of input,
    setting up networks connections and such would require a dummy line from
    the user starting the program.
    To make daemon programming more convenient, the special address 0 is
    added. Before accepting input, any commands or blocks for line 0 will
    be run. Unconditional commands will not be run for the pre-first line,
    but unconditional blocks will (e.g. if they contain other commands or
    blocks with line 0 as the address).
    This special handling should mean that conventional sed programs don't
    change behavior when run by extended sed.

    During handling the pre-first lines, no regexps will be considered to
    match pattern space.

* `I` - Interrupt/IPC

    When starting a cycle, if there are pending IPC messages to process,
    the I address will match. Pattern space will not match any ordinary
    regexps for this cycle, and like the other special address, when this
    would match, unconditional commands are not run.

    Inside blocks with the I address, expressions will match against the
    interrupt message instead of pattern space.

    (See also the m command.)

## Added commands

Only commands added over GNU sed (or significantly altered) will be documented
here.

### I/O commands

Extending GNU sed, sedition supports multiple files to be opened and used. This
is primarily useful for networking, replacing stdin/stdout with a socket, but
may eventually be used with files as well.

Files are identified by an arbitrary integer assigned by the program. In
command descriptions, these are usually called `fd`.

Unlike your traditional stdin/stdout file descriptors, all file descriptors are
bidirectional and the initial state, `0` refers to both stdin and stdout
depending on the direction of I/O. This neatly maps to sockets.

* `< fd1 [fd2]`

  Close file descriptor fd1 and (in the two operand form) rename fd2 to fd1.

* `n [fd]` and `N [fd]`

  Read a line from the given file descriptor into pattern space.

  If no operand is given, the file descriptor to use defaults to 0. This will
  work like the `n` and `N` from sed.

* `p [fd]`

  Output pattern space to the given file descriptor. If no file descriptor is
  given, print to file 0.

### Networking

* `L sfd [host]:port`

  Listen for TCP connections on the given host and port. If `host` is empty,
  listen on all interfaces.

  `sfd` will be the server file descriptor, and can be used with `< sfd` to
  close it, or with `A sfd cfd` to accept incoming client connections.

* `A sfd cfd`

  Accept a connection on server socket `sfd`, name it `cfd`. Closes any file
  previously open with number `cfd`.

  `sfd` must be a file descriptor previously opened for listening using `L`.

### Threading and messaging

* `f [addr] cmd`

  Start a new thread, using `cmd` as its program. The program may be a block,
  a command without address, or (as in the echo server example) a single
  command with an address.

  Hold space and file descriptors is inherited from the forked thread, but
  changes from the thread will only be visible in that thread.
  The line number is reset, and the forked program starts by running pre-first
  line commands.

  The forked program runs until EOF on file descriptor 0. In a network server,
  the forked program usually starts by redirecting a socket to fd 0 and using
  that as the standard input.

  If the command is a block, reaching the end of the block will start a new
  cycle of input from that thread's file descriptor 0, restarting at the start
  of the block rather than the beginning of the program.

  Jumps out of the block should lead to a jump back into the block, but
  interesting effects can be achieved by not doing that. For example, reaching
  the end of another thread's block will restart processing at the beginning of
  *that* block instead of the one that started the thread. Likewise, reaching
  the end of the program will restart processing at the start of the whole
  program, not at the start of the thread's block.

* `m [message]`

  Broadcast `message` as an IPC message to all running threads. The next cycle
  of all threads will process the message instead of a line of input.

  If no message is given, the current pattern space will be broadcast instead.

### Extended hold-space

`g`, `G`, `h`, `H` and `x` are extended to take an optional register name. When
used without the name, these correspond to the usual sed commands modifying the
hold space. When used with names, each name identifies its own hold space.

Hold spaces are separate for each thread, but inherit the previously set values
from whatever thread created them.

#### Special registers

* The `yhjulwwiefzojcbxybbruweejw` register contains a new random string each
  time it is read, currently consisting of 32 characters in the range A-Z.

  Note that while the name may *appear* completely random, it is only pseudorandom.
