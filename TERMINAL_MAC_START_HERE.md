# Mac Terminal walkthrough: first Lean checkpoint and GitHub preparation

This guide is for Alex Chan and assumes a Mac. Do one numbered step at a time.
Wait for each command to finish before typing the next. A line ending in `%`
is the Terminal prompt; it usually means the previous command has finished.
You do not type the `%`. If a command reports an error, stop and send its
complete output to this chat. Do not change versions or delete files to guess
at a fix.

The paper has a human-readable proof. The Python program checks finite graphs.
The new Lean file is a **first proof candidate for the eight-vertex graph**.
I could not run Lean in the preparation environment. The entire classification
has not been formalized, and a successful first build would verify only this
finite checkpoint. The README and manuscript disclose that status.

## A. Unpack the project

1. Download `Krebs_Sankar_Q53_terminal_lean_starter.zip` from this chat.
   Safari or Chrome normally puts it in Downloads. If Safari automatically
   unzips it and removes the ZIP, use the extracted folder instead: run
   `mv ~/Downloads/krebs-sankar-q53-lean-starter ~/Documents/` in Terminal,
   then continue at step 6. Stop if Documents already contains a folder with
   that name; do not overwrite it.
2. Open **Terminal** on your Mac: press Command-Space, type `Terminal`, and
   press Return. The next steps use Terminal, without VS Code.
3. Paste this command and press Return:

   ```sh
   cd ~/Downloads
   ```

4. Check that the ZIP is there:

   ```sh
   ls Krebs_Sankar_Q53_terminal_lean_starter.zip
   ```

   You should see its name. If the file has a different name, stop and tell
   me what `ls` displays in Downloads; do not type an approximate name.
5. Extract it into Documents:

   ```sh
   unzip -n Krebs_Sankar_Q53_terminal_lean_starter.zip -d ~/Documents
   ```

6. Go into the extracted folder:

   ```sh
   cd ~/Documents/krebs-sankar-q53-lean-starter
   ```

7. Confirm your location:

   ```sh
   pwd
   ```

   The last part should be `Documents/krebs-sankar-q53-lean-starter`.
8. Confirm the important files are present:

   ```sh
   ls
   ```

   You should see `lakefile.toml`, `lean-toolchain`, `Audit.lean`,
   `KrebsSankarQ53.lean`, `KrebsSankarQ53` (a folder), and the paper.

Keep this Terminal window in that folder for the remaining steps. If you
close it, repeat step 6 before running a project command.

## B. Run the graph checks you can do immediately

9. Check whether Python 3 is available:

   ```sh
   python3 --version
   ```

   A version number means it is installed. If it says `command not found`,
   install Python 3 from https://www.python.org/downloads/macos/ and open a
   new Terminal window. Repeat steps 6 and 9.
10. Run the checks:

    ```sh
    python3 verify_small.py
    ```

    The result should show `three_chromatic: 0` for both the 16-set and
    512-set searches, plus a `D8_witness` with `nonbipartite: true`.
    The program also rewrites `finite_verification.json`. This is a
    computational check of small cases, not a Lean proof.

## C. Install Lean, once

11. Check whether Git is installed:

    ```sh
    git --version
    ```

    On a new Mac this may ask you to install Apple's Command Line Tools.
    Accept the prompt, wait for completion, then run `git --version` again.
12. Install Lean's version manager, `elan`, using the command on Lean's
    official manual-install page (https://lean-lang.org/install/manual/):

    ```sh
    curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
    ```

    If asked to select an installation option, type `1` and Return. It may
    download a compiler. Wait for the Terminal prompt to return.
13. Tell this Terminal window where the new commands live:

    ```sh
    source "$HOME/.elan/env"
    ```

14. Check Lake, Lean's project builder:

    ```sh
    lake --version
    ```

    A version number is success. A `command not found` error means the
    installation needs attention; send me the message.

## D. Ask Lean to check the first graph proof

You should still be in `~/Documents/krebs-sankar-q53-lean-starter`.
The project pins Lean and Mathlib to matching version 4.29.0. The first
download may take time and disk space.

15. Get the project's mathematical library and write the dependency lock file:

    ```sh
    lake update
    ```

    Wait for the `%` prompt. This also creates `lake-manifest.json`, which
    belongs in the eventual GitHub upload. It is normal to see many downloads.
16. Get prebuilt mathematical library files:

    ```sh
    lake exe cache get
    ```

    Wait for the `%` prompt. If you see no progress for several minutes,
    open a *second* Terminal window to ask me what to inspect; leave the
    first command running and send its last lines.

    You can prepare GitHub in parallel: open a second Terminal window,
    run `cd ~/Documents/krebs-sankar-q53-lean-starter` there, and do steps
    19-20 below. Wait until `lake update` has finished before step 21 so
    the dependency lock file is included. The two Terminal windows do not
    need to be closed when the other is working.
17. Compile the finite witness and project entry point:

    ```sh
    lake build
    ```

    **Success:** it ends without `error` and the `%` prompt returns.
    **Failure:** copy the entire error, including the file and line number,
    into this chat. I will fix the exact Lean code with you. I have not run
    this build myself, so a correction may be needed on your Mac.
18. If step 17 succeeded, run the audit:

    ```sh
    lake env lean Audit.lean
    ```

    It should print the name and type of
    `KrebsSankarQ53.concrete_cayley_witness` and its axioms. Read the output;
    do not treat merely seeing `%` as a proof of the paper. Send the entire
    audit output here so I can check the exact statement and assumptions.

At that point we will have a checked finite starting point if both commands
pass. Next I will work through section lifting, the structural dichotomy,
and the quaternionic obstruction in separate Lean modules. That is substantial
additional work. Do not describe the paper as fully Lean verified yet.

## E. Prepare a clean GitHub upload in Terminal

You can do this while the Lean work continues. You need not wait for the
general theorem. The README clearly says which pieces are pending.

19. From the project folder, initialize Git:

    ```sh
    git init
    ```

20. Set the name and email for **this project**:

    ```sh
    git config user.name "Alex Chan"
    ```

    ```sh
    git config user.email "achan@hbs.edu"
    ```

21. Add the project files to the proposed commit:

    ```sh
    git add .
    ```

22. Inspect exactly what will be uploaded:

    ```sh
    git status --short
    ```

    You should see the manuscript, Python program, Lean source,
    `lakefile.toml`, `lean-toolchain`, README, and (after step 15)
    `lake-manifest.json`. You should **not** see `.lake/`, downloaded
    dependencies, or LaTeX `.aux` and `.log` files. If you see an unfamiliar
    or private file, stop here and send me the list before committing.
23. Commit the exact files you saw:

    ```sh
    git commit -m "Add manuscript and finite Lean witness starter"
    ```

24. Name the branch `main`:

    ```sh
    git branch -M main
    ```

    A commit saves a version on your Mac. It has **not** uploaded to GitHub.

## F. Publish to your own GitHub account from Terminal

25. Check whether the GitHub command-line app is installed:

    ```sh
    gh --version
    ```

    If it prints a version, continue. If it says `command not found`, check
    for Homebrew with `brew --version`. If Homebrew exists, run `brew install gh`.
    If Homebrew is also missing, its official terminal installer is:

    ```sh
    /bin/bash -c "$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/HEAD/install.sh)"
    ```

    Read its prompts and press Return when asked. After installation, run
    these two lines, one at a time (the first makes `brew` visible in this
    Terminal on either common Mac architecture):

    ```sh
    if [ -x /opt/homebrew/bin/brew ]; then eval "$(/opt/homebrew/bin/brew shellenv)"; elif [ -x /usr/local/bin/brew ]; then eval "$(/usr/local/bin/brew shellenv)"; fi
    ```

    ```sh
    brew install gh
    ```

    Run `gh --version` again. Stop and send me the output if any step fails.
26. Sign in through the GitHub CLI:

    ```sh
    gh auth login
    ```

    Choose **GitHub.com**, **HTTPS**, and **Login with a web browser** when
    asked. A browser page for authentication may open; this is normal even
    though all work was started in Terminal. Do not paste your password or
    a login code into this chat.
27. Confirm the account shown is `alexgocardinal`:

    ```sh
    gh auth status
    ```

    Stop if it shows a different account.
28. Check whether the proposed repository name already exists:

    ```sh
    gh repo view alexgocardinal/krebs-sankar-q53
    ```

    A `repository not found` message means the name is available; proceed.
    If you see an existing repository, **stop** and send me that output.
    Do not overwrite or merge another project by guessing.
29. If the repository does not exist, publish this folder:

    ```sh
    gh repo create alexgocardinal/krebs-sankar-q53 --public --source=. --remote=origin --push
    ```

    This creates a public repository and pushes the local commit. The status
    of the Lean work is stated honestly in the README.
30. Check the online address:

    ```sh
    gh repo view alexgocardinal/krebs-sankar-q53 --web
    ```

    It should open your repository in a browser. Confirm the files and README
    are visible. Send me the repository link or the output of step 29.

The revised paper currently links your *existing GitHub profile*. After your
repository actually exists, I can replace that with the direct repository URL
and, once the Lean proof is complete, cite a fixed commit. Publishing the
starter project does not turn it into a proof of the general classification.

## A useful rule for every step

If Terminal shows only `%`, the command likely finished. If it displays
`error`, `failed`, or `Traceback`, stop and paste the whole message into this
chat. If it is still running, leave the window open. Your files remain on
disk after a restart, but an interrupted command may need to be rerun.
