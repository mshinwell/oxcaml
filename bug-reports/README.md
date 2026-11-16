# Compiler bug reports

Each directory `bugs/<slug>/` describes one bug of the compiler, the runtime
or the standard library, with a test that shows it. `create_issues.py`
(Python 3, standard library only) turns them into GitHub issues. The
candidate fixes were built and tested together on an earlier tree; each
applies to this one. Every test was verified against OxCaml main at 07a23cd839.

    bugs/<slug>/bug.json   the description
    bugs/<slug>/test.ml    the test (more files only where the bug needs them)
    bugs/<slug>/fix.diff   a candidate fix, if there is one; `git apply` at the top of the tree

Fields of `bug.json`: `title`; `category` (`wrong-code`, `crash`,
`lost-tail-call`, `compiler-error`, `runtime`, `stdlib`, `performance`,
`diagnostic`, `question`); `summary`; `commands` (run in order by `sh` in the
directory, with `ocamlopt` and `ocamlc` from `PATH`); `reference_commands`
(optional: a run that gives the expected result); `expected` and `actual`
(`text` for the issue, and for `--verify` the `output` that the commands
print, as substrings, and their `exit` status); `affects` (which of
`bytecode`, `-Oclassic`, default, `-O2`, `-O3` show it, the `flags` it needs,
and whether `-flambda2-expert-cmm-safe-subst` changes it: `no`, `fixes` or
`needed`); `upstream` (whether OCaml 5.4.0 has it too: `true`, `false`, or
`null` if not compared); `cause` (optional); `fix` (`null`, or the file and one
sentence on it); `labels` (suggested; those the repository lacks are dropped);
`status` (`open`, `known` to the developers, or `fixed`; optional `reference`).

    python3 create_issues.py                     # dry run: title and body of each issue
    python3 create_issues.py --verify PREFIX     # run each test with the compiler installed at PREFIX
    python3 create_issues.py --create --repo OWNER/NAME [--verify PREFIX]

`--verify` says for each bug whether its commands give the `actual` result
(bug present), the `expected` one (fixed), or something else; with `--create`
only the bugs present are filed. `--create` uses `gh` if it is on `PATH`,
otherwise the REST API with `GITHUB_TOKEN`; it records slug -> issue URL in
`issues-state.json` (`--state FILE`) and skips the slugs already recorded, so
it can be run again after a failure. It files `open` bugs, `known` ones only
with `--include-known`, and never `fixed` ones.

Selection: `--only SLUG...`, `--category C`, `--skip-upstream`,
`--skip-questions`; `--no-fix` leaves the fixes out of the bodies.
