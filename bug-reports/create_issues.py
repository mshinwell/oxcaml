#!/usr/bin/env python3
"""File the bug reports of bugs/*/ as GitHub issues.  See README.md."""

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import urllib.request

HERE = os.path.dirname(os.path.abspath(__file__))
BUGS = os.path.join(HERE, "bugs")
CATEGORIES = ["wrong-code", "crash", "lost-tail-call", "compiler-error",
              "runtime", "stdlib", "performance", "diagnostic", "question"]
WAYS = ["bytecode", "-Oclassic", "default", "-O2", "-O3"]
SAFE_SUBST = ["no", "fixes", "needed"]
STATUSES = ["open", "known", "fixed"]
NOT_TEST_FILES = {"bug.json", "fix.diff"}
LANG = {".ml": "ocaml", ".mli": "ocaml", ".c": "c", ".sh": "sh"}


def fail(msg):
    sys.exit("error: " + msg)


def need(cond, slug, msg):
    if not cond:
        fail(f"{slug}: {msg}")


def is_strings(v):
    return isinstance(v, list) and all(isinstance(s, str) for s in v)


def check_outcome(slug, name, o):
    need(isinstance(o, dict) and isinstance(o.get("text"), str), slug,
         f"{name} must be an object with a string 'text'")
    out = o.get("output", [])
    o["output"] = out = [out] if isinstance(out, str) else out
    need(is_strings(out), slug, f"{name}.output must be a string or a list of strings")
    need(isinstance(o.get("exit", 0), int), slug, f"{name}.exit must be an integer")
    need(out or "exit" in o, slug, f"{name} needs 'output' or 'exit'")


FIELDS = {"title", "category", "summary", "commands", "reference_commands",
          "expected", "actual", "affects", "upstream", "cause", "fix",
          "labels", "status", "reference"}


def load(slug):
    d = os.path.join(BUGS, slug)
    need(re.fullmatch(r"[a-z0-9]+(-[a-z0-9]+)*", slug), slug,
         "a slug is lower case words joined by hyphens")
    try:
        with open(os.path.join(d, "bug.json")) as f:
            b = json.load(f)
    except (OSError, ValueError) as e:
        fail(f"{slug}: cannot read bug.json: {e}")
    for k in b:
        need(k in FIELDS, slug, f"unknown field {k!r}")
    for k in ["title", "summary"]:
        need(isinstance(b.get(k), str) and b[k].strip(), slug, f"{k} must be a non-empty string")
    need("\n" not in b["title"], slug, "the title is one line")
    need(b.get("category") in CATEGORIES, slug, f"category must be one of {', '.join(CATEGORIES)}")
    b.setdefault("reference_commands", [])
    for k in ["commands", "reference_commands"]:
        need(is_strings(b.get(k)), slug, f"{k} must be a list of strings")
    need(b["commands"], slug, "commands is empty")
    check_outcome(slug, "expected", b.get("expected"))
    check_outcome(slug, "actual", b.get("actual"))
    a = b.get("affects")
    need(isinstance(a, dict) and all(isinstance(a.get(w), bool) for w in WAYS), slug,
         f"affects must give true or false for each of {', '.join(WAYS)}")
    need(is_strings(a.get("flags", [])), slug, "affects.flags must be a list of strings")
    need(a.get("safe-subst") in SAFE_SUBST + [None], slug,
         f"affects.safe-subst must be one of {', '.join(SAFE_SUBST)} or null")
    need(b.get("upstream") in (True, False, None), slug, "upstream must be true, false or null")
    need(isinstance(b.get("cause", ""), str), slug, "cause must be a string")
    fx, has_diff = b.get("fix"), os.path.isfile(os.path.join(d, "fix.diff"))
    need(fx is None or (isinstance(fx, dict) and fx.get("file") == "fix.diff"
                        and isinstance(fx.get("text"), str)), slug,
         "fix must be null or {'file': 'fix.diff', 'text': ...}")
    need((fx is not None) == has_diff, slug, "fix and the file fix.diff must go together")
    b.setdefault("status", "open")
    need(b["status"] in STATUSES, slug, f"status must be one of {', '.join(STATUSES)}")
    need(isinstance(b.get("reference", ""), (str, int)), slug,
         "reference must be a URL or a pull-request number")
    b.setdefault("labels", [])
    need(is_strings(b["labels"]), slug, "labels must be a list of strings")
    b["files"] = sorted((f for f in os.listdir(d) if f not in NOT_TEST_FILES),
                        key=lambda f: (f != "test.ml", f))
    if "test.ml" not in b["files"]:
        fail(f"{slug}: test.ml is missing")
    b["slug"], b["dir"] = slug, d
    return b


def fence(text, lang=""):
    ticks = "```"
    while ticks in text:
        ticks += "`"
    return f"{ticks}{lang}\n{text.rstrip()}\n{ticks}\n"


def body(b, with_fix=True):
    out = [b["summary"].strip(), "", "### Reproduce", ""]
    for f in b["files"]:
        with open(os.path.join(b["dir"], f)) as fh:
            src = fh.read()
        out += [f"`{f}`:", "", fence(src, LANG.get(os.path.splitext(f)[1], ""))]
    out += [fence("\n".join(b["commands"]), "sh")]
    if b["reference_commands"]:
        out += ["A run that gives the expected result:", "",
                fence("\n".join(b["reference_commands"]), "sh")]
    out += [f"**Expected:** {b['expected']['text']}", "",
            f"**Actual:** {b['actual']['text']}", "", "### Affects", ""]
    a = b["affects"]
    out += ["| " + " | ".join(WAYS) + " |", "|" + "---|" * len(WAYS),
            "| " + " | ".join("yes" if a[w] else "no" for w in WAYS) + " |", ""]
    if a.get("flags"):
        out.append("Needs: " + ", ".join(f"`{x}`" for x in a["flags"]) + ".")
    s = a.get("safe-subst")
    if s is not None:
        out.append("With `-flambda2-expert-cmm-safe-subst`: " + {
            "no": "the same.", "fixes": "right.",
            "needed": "only with that flag."}[s])
    up = b["upstream"]
    out += ["Upstream OCaml 5.4.0: " + {True: "has the same bug.", False: "not affected.",
                                         None: "not compared."}[up], ""]
    if b.get("reference"):
        ref = str(b["reference"])
        out += [ref[:1].upper() + ref[1:] + ".", ""]
    if b.get("cause"):
        out += ["### Cause", "", b["cause"].strip(), ""]
    if with_fix and b.get("fix"):
        with open(os.path.join(b["dir"], "fix.diff")) as fh:
            diff = fh.read()
        out += ["<details><summary>Candidate fix</summary>", "",
                b["fix"]["text"].strip(), "", fence(diff, "diff"), "</details>", ""]
    return "\n".join(out).rstrip() + "\n"


def run_commands(b, prefix, timeout):
    work = tempfile.mkdtemp(prefix="bug-")
    try:
        for f in b["files"]:
            shutil.copy(os.path.join(b["dir"], f), work)
        env = dict(os.environ)
        env["PATH"] = os.path.join(prefix, "bin") + os.pathsep + env.get("PATH", "")
        script = "set -e\n" + "\n".join(b["commands"]) + "\n"
        try:
            p = subprocess.run(["sh", "-c", script], cwd=work, env=env,
                               stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                               timeout=timeout)
        except subprocess.TimeoutExpired as e:
            return None, (e.stdout or b"").decode(errors="replace")
        code = p.returncode if p.returncode >= 0 else 128 - p.returncode
        return code, p.stdout.decode(errors="replace")
    finally:
        shutil.rmtree(work, ignore_errors=True)


def matches(o, code, output):
    if "exit" in o and o["exit"] != code:
        return False
    return all(s in output for s in o["output"])


def verify(bugs, prefix, timeout):
    """Prints a verdict for each bug; returns the slugs where the bug is present."""
    if not os.path.isfile(os.path.join(prefix, "bin", "ocamlopt")):
        fail(f"no {prefix}/bin/ocamlopt")
    counts, present = {}, set()
    for b in bugs:
        code, output = run_commands(b, prefix, timeout)
        if code is None:
            verdict = "other (timed out)"
        elif matches(b["actual"], code, output):
            verdict = "bug present"
            present.add(b["slug"])
        elif matches(b["expected"], code, output):
            verdict = "fixed"
        else:
            verdict = "other"
        counts[verdict.split(" (")[0]] = counts.get(verdict.split(" (")[0], 0) + 1
        print(f"{b['slug']}: {verdict}")
        if verdict.startswith("other"):
            tail = output.strip().splitlines()[-5:]
            print(f"    exit {code}; last lines:")
            for line in tail:
                print("    | " + line[:200])
    print("total: " + ", ".join(f"{k} {v}" for k, v in sorted(counts.items())))
    return present


def gh_labels_and_create(repo):
    if shutil.which("gh"):
        p = subprocess.run(["gh", "label", "list", "--repo", repo, "--limit", "1000",
                            "--json", "name", "--jq", ".[].name"],
                           stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        existing = set(p.stdout.split("\n")) if p.returncode == 0 else set()

        def create(title, text, labels):
            cmd = ["gh", "issue", "create", "--repo", repo, "--title", title,
                   "--body-file", "-"]
            for lab in labels:
                cmd += ["--label", lab]
            p = subprocess.run(cmd, input=text, stdout=subprocess.PIPE,
                               stderr=subprocess.PIPE, text=True)
            if p.returncode != 0:
                raise RuntimeError(p.stderr.strip())
            return p.stdout.strip().splitlines()[-1]
        return existing, create
    token = os.environ.get("GITHUB_TOKEN")
    if not token:
        fail("neither gh on PATH nor GITHUB_TOKEN in the environment")
    api = "https://api.github.com/repos/" + repo

    def call(method, url, data=None):
        req = urllib.request.Request(
            url, method=method, data=None if data is None else json.dumps(data).encode(),
            headers={"Authorization": "Bearer " + token,
                     "Accept": "application/vnd.github+json"})
        with urllib.request.urlopen(req) as r:
            return json.load(r)
    existing, page = set(), 1
    try:
        while True:
            got = call("GET", f"{api}/labels?per_page=100&page={page}")
            existing |= {lab["name"] for lab in got}
            if len(got) < 100:
                break
            page += 1
    except Exception:
        existing = set()

    def create(title, text, labels):
        return call("POST", api + "/issues",
                    {"title": title, "body": text, "labels": labels})["html_url"]
    return existing, create


def create_all(bugs, repo, state_file, with_fix):
    state = {}
    if os.path.exists(state_file):
        with open(state_file) as f:
            state = json.load(f)
    existing, create = gh_labels_and_create(repo)
    for b in bugs:
        if b["slug"] in state:
            print(f"{b['slug']}: already filed, {state[b['slug']]}")
            continue
        labels = [lab for lab in b["labels"] if lab in existing]
        try:
            url = create(b["title"], body(b, with_fix), labels)
        except Exception as e:
            fail(f"{b['slug']}: {e} (state kept in {state_file}; run again to go on)")
        state[b["slug"]] = url
        with open(state_file, "w") as f:
            json.dump(state, f, indent=2, sort_keys=True)
        print(f"{b['slug']}: {url}")


def why_skipped(b, args):
    if b["status"] == "fixed":
        return "status fixed"
    if b["status"] == "known" and not args.include_known:
        return "status known (--include-known files it)"
    if args.skip_upstream and b["upstream"] is True:
        return "upstream OCaml has it too"
    if args.skip_questions and b["category"] == "question":
        return "a question"
    return None


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--create", action="store_true", help="file the issues")
    ap.add_argument("--repo", help="OWNER/NAME, with --create")
    ap.add_argument("--state", default=os.path.join(HERE, "issues-state.json"),
                    help="file of slug -> issue URL (default: %(default)s)")
    ap.add_argument("--only", nargs="+", metavar="SLUG")
    ap.add_argument("--category", choices=CATEGORIES)
    ap.add_argument("--skip-upstream", action="store_true",
                    help="leave out bugs that upstream OCaml has too")
    ap.add_argument("--skip-questions", action="store_true")
    ap.add_argument("--include-known", action="store_true",
                    help="also file bugs whose status is known")
    ap.add_argument("--no-fix", action="store_true", help="no candidate fix in the body")
    ap.add_argument("--verify", metavar="PREFIX",
                    help="run the commands with the compiler installed at PREFIX; "
                    "with --create, file only the bugs present there")
    ap.add_argument("--timeout", type=int, default=300, help="seconds per bug, --verify")
    ap.add_argument("--dir", help="the directory of bug directories (default: bugs/)")
    args = ap.parse_args()
    global BUGS
    if args.dir:
        BUGS = os.path.abspath(args.dir)
    slugs = sorted(os.listdir(BUGS))
    if args.only:
        for s in args.only:
            if s not in slugs:
                fail(f"no bug {s}")
        slugs = [s for s in slugs if s in args.only]
    bugs = [load(s) for s in slugs]
    if args.category:
        bugs = [b for b in bugs if b["category"] == args.category]
    skipped = []
    if args.create or not args.verify:
        kept = []
        for b in bugs:
            why = why_skipped(b, args)
            if why:
                skipped.append((b["slug"], why))
            else:
                kept.append(b)
        bugs = kept
    if args.create:
        if not args.repo or not re.fullmatch(r"[\w.-]+/[\w.-]+", args.repo):
            fail("--create needs --repo OWNER/NAME")
        if args.verify:
            present = verify(bugs, os.path.abspath(args.verify), args.timeout)
            skipped += [(b["slug"], "not present with that compiler (above)")
                        for b in bugs if b["slug"] not in present]
            bugs = [b for b in bugs if b["slug"] in present]
        for slug, why in skipped:
            print(f"skipped {slug}: {why}")
        create_all(bugs, args.repo, args.state, not args.no_fix)
    elif args.verify:
        verify(bugs, os.path.abspath(args.verify), args.timeout)
    else:
        for b in bugs:
            print("=" * 72)
            print(f"[{b['slug']}] {b['title']}")
            print("labels: " + ", ".join(b["labels"]))
            print("-" * 72)
            print(body(b, not args.no_fix))
        for slug, why in skipped:
            print(f"skipped {slug}: {why}")
        print(f"{len(bugs)} issues, {len(skipped)} skipped "
              "(dry run; --create --repo OWNER/NAME files them)")


if __name__ == "__main__":
    main()
