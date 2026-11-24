"""Generate split kernel checks for the optional extended two-rise grid."""

from pathlib import Path
from sys import argv


GRID = (688, 1105, 1766, 2814, 4475, 7107, 11279, 17891, 28371,
        44982, 71309, 113037, 179174)


def module(points, reduced=False):
    checker, width = ("reducedRange", 24) if reduced else ("rangeCheck", 32)
    dependency = "ReducedHeight" if reduced else "FastHeight"
    out = [
        f"import {dependency}", "",
        "namespace Cycle108", "", "open Collatz.TwoRise", "",
        "set_option maxRecDepth 12000", "set_option maxHeartbeats 0",
        "set_option Elab.async false",
        "",
    ]
    for k in points:
        b = k + 24
        names = []
        for start in range(1, k + 1, 700):
            count = min(700, k + 1 - start)
            w = 2 * (k + 1 - start if reduced else k) + 101
            name = f"r{k}_{start}"
            names.append(name)
            inv = f"powMod (2^{w}) 21 ((2^{w}+1)/3) {start-1} 1"
            out.extend([
                f"private theorem {name} : RangeCond {k} {b} {start} {start+count} := by",
                f"  exact {checker}_sound (show {checker} {k} {b} {width} {w}",
                f"    ({start}) ({inv}) {count} = true by decide +kernel)",
                "",
            ])
            if reduced and len(names) % 24 == 0:
                out.extend([f'#eval IO.println "N = {k}, checked through {start+count-1}"', ""])
        out.append(f"theorem pairs{k} : AllPairs {k} {b} := by")
        out.append("  apply allPairs_of_range")
        out.append("  exact " + balanced(names))
        out.append("")
    out += [f"#print axioms pairs{points[-1]}", "", "end Cycle108", ""]
    return "\n".join(out)


def balanced(proofs):
    if len(proofs) == 1:
        return proofs[0]
    mid = len(proofs) // 2
    return (f"(RangeCond.trans {balanced(proofs[:mid])} "
            f"{balanced(proofs[mid:])})")


if __name__ == "__main__":
    name, first, last, *mode = argv[1:]
    path = Path(__file__).resolve().with_name(name + ".lean")
    path.write_text(module(GRID[int(first):int(last)], mode == ["reduced"]), encoding="utf-8")
