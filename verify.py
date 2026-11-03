"""Build the included proof sources and reject nonstandard axioms."""
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parent


def run(*args):
    subprocess.run(["lake", "--no-cache", *args], cwd=ROOT, check=True)


def main():
    libraries = [
        (ROOT, "MsetsPaper"),
        (ROOT, "MsetsLower"),
        (ROOT / "vendor/coefficient-one", "CoefficientOne"),
        (ROOT / "vendor/coefficient-one", "EffectiveResistance"),
        (ROOT / "vendor/coefficient-one", "AlgebraicCombinatorics"),
    ]
    modules = set()
    for base, name in libraries:
        paths = list((base / name).rglob("*.lean"))
        if (base / (name + ".lean")).is_file():
            paths.append(base / (name + ".lean"))
        if not paths:
            raise RuntimeError("Missing proof library: " + name)
        modules.update(".".join(p.relative_to(base).with_suffix("").parts) for p in paths)
    modules = sorted(modules)
    # Keep each command below Windows' command-line length limit.
    for start in range(0, len(modules), 80):
        run("build", *modules[start:start + 80])
    check = ROOT / ".lake/verification/Check.lean"
    check.parent.mkdir(parents=True, exist_ok=True)
    imports = "".join("import " + name + "\n" for name in modules)
    check.write_text(imports + r'''
import Lean.Util.CollectAxioms

open Lean in
set_option maxHeartbeats 0 in
run_elab do
  let env ← getEnv
  let names := env.constants.toList.map Prod.fst |>.filter fun n =>
    match env.getModuleIdxFor? n with
    | none => false
    | some idx =>
      let origin := env.header.moduleNames[idx.toNat]!
      (`MsetsPaper).isPrefixOf origin || (`MsetsLower).isPrefixOf origin ||
      (`CoefficientOne).isPrefixOf origin || (`EffectiveResistance).isPrefixOf origin ||
      (`AlgebraicCombinatorics).isPrefixOf origin
  if names.isEmpty then
    throwError "No project declarations were imported"
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  for n in names do
    for ax in (← collectAxioms n) do
      unless ax ∈ allowed do
        throwError "Disallowed axiom {ax} in {n}"
  logInfo m!"Checked axioms of {names.length} declarations."
''', encoding="utf-8", newline="\n")
    run("env", "lean", str(check))
    print("Build and axiom check passed.")


if __name__ == "__main__":
    main()
