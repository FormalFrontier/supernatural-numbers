#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Authors: Formal Frontier Agents
"""Bounded native doc-gen4 Markdown adapter for Supernatural Numbers.

Adapted by worker-b from polynomial-root-stability d31add515b6fd4a55612241a5b0f470c129cc467,
with Beacon's source-only correction f7ef00335857f1a22e0a241a57398b98f40f180a;
that adapter credited Anchor's ideal-completion recipe f0c8c34386109116e4912fb425a8ad15d9dc42a4.
The independent raw native records and generation commands remain necessary review inputs.
"""

if not __debug__:
    raise SystemExit("optimized Python is not supported for API generation")

import argparse
import hashlib
from html.parser import HTMLParser
import json
from pathlib import Path
import re

TOOL = "97d4ecdfc8e09e7f511724c25e303d448de6a3db"
SOURCE = "cc3e8d151c87585111df3abe6d2c40d9f10971c6"
SOURCE_TREE = "15e99ee28ce447f921b0e74f9ad71e3ce85509b5"
MODULES = (
    'SupernaturalNumbers.Basic',
    'SupernaturalNumbers.NatEmbedding',
    'SupernaturalNumbers.Order',
    'SupernaturalNumbers.Tower',
    'SupernaturalNumbers.Characters',
    'SupernaturalNumbers',
    'SupernaturalNumbersTests.ReleaseClients',
    'SupernaturalNumbersTests',
)
INPUTS = tuple(module.replace(".", "/") + ".lean" for module in MODULES) + (
    "lean-toolchain", "lakefile.toml", "lake-manifest.json",
)
INPUT_SHA256 = {
    'SupernaturalNumbers/Basic.lean': 'cc7f4804002fc29e505aacdf4ff614c1fcca0c5bdc431ad94d8eb822ae80cf7c',
    'SupernaturalNumbers/NatEmbedding.lean': '939364c7dda228285eefc18d79e2d31294fce4cb15d2c190ddd02bae6f5719e7',
    'SupernaturalNumbers/Order.lean': 'e1edd3730bcc3f8f9bfa48202fa0a3e6cf1468698c2ba5d9395a146b6f783d53',
    'SupernaturalNumbers/Tower.lean': 'a2c929c163a9806a1657eedb0910d8c538716e1ee0c2b614525de6b26199008a',
    'SupernaturalNumbers/Characters.lean': '5555749e5972b7c4f3c7970b430481c1aae97f10dd1ee050480c52fa744a26fc',
    'SupernaturalNumbers.lean': '47c15eee1f1107a28263a073d7afcefb4a66f31649afd1cfc7c23cd813ad41b0',
    'SupernaturalNumbersTests/ReleaseClients.lean': '40fecb453e1fafdee3e9f3974658f8a5878e8f002a64188bc5df82c442781b50',
    'SupernaturalNumbersTests.lean': 'b1313fb46062b0189216cb1e1d8e83593d0e50db1e4144696cc87c3fc44892bd',
    'lean-toolchain': '8190e75a201741065fe508b28955dd64dd72d090babe5f70ce6848879d68ae88',
    'lakefile.toml': '55ad6c534778dd5041c89b0d7dc49a3c416c3b4208cb4837d248963b3ffa2ddc',
    'lake-manifest.json': '985257bd3394888a823175dea207fb616b0a965a01932568fdffe529b027dc3e',
}
NATIVE_SHA256 = {
    'SupernaturalNumbers.Basic': '3b5a35a213a43c2b0a8fe8a4e1b3159f7a7e5df0b26b13d0e3638cba575fb025',
    'SupernaturalNumbers.NatEmbedding': '72cbf11b674b4d7c7dedf0d48175c451c722f0294b54db7ca1f3b1fc94879556',
    'SupernaturalNumbers.Order': '595ab312931dfaa15c3487a0bb2c65008bbc531b5ea1892d9188876064353c04',
    'SupernaturalNumbers.Tower': 'fd326985b3e298f7d4f424e7f20b9eb82c76a811022b8112e2893f1fd5f07e71',
    'SupernaturalNumbers.Characters': '5abea3ab813003e661469f8b54132f2d846f79879d6776dd9c31e57a319dd1bd',
    'SupernaturalNumbers': '796f7e057734b6901843f22fb1766f6e379b2f45965fc78e0a3a2e4da838897a',
    'SupernaturalNumbersTests.ReleaseClients': 'cbd1a9d9a17614b8fab0fa7524920032a093ea6796f20e3b4ec98bab11dafdd5',
    'SupernaturalNumbersTests': '3d7c2dc83647ada0e3eea585ad8f50b6cc5284ad46b256591cd79022b6880e65',
}
COUNTS = (26, 19, 16, 15, 28, 0, 16, 0)
GENERATED = "Supernatural.ext_iff"
UNDOCUMENTED_INSTANCE = "Supernatural.instCompleteLattice"
INSTANCE_EXPLANATION = ("Original catalogue explanation (not a native docstring): the complete "
    "lattice transports the pointwise `ℕ∞` lattice across the multiplicative type tag. "
    "Its bottom is one, as witnessed by `Supernatural.bot_eq_one`.")
KEY_SIGNATURES = {
    "Supernatural.exponent_iSup": ("{ι : Sort", "(f : ι → Supernatural)", "⨆"),
    "Supernatural.exponent_iInf": ("{ι : Sort", "(f : ι → Supernatural)", "⨅"),
    "Supernatural.iProd": ("{ι : Type", "(f : ι → Supernatural)"),
    "Supernatural.instCompleteLattice": ("CompleteLattice Supernatural",),
    "Supernatural.bot_eq_one": ("⊥ = 1",),
    "Supernatural.ofPNat": ("(n : ℕ+)",),
    "Supernatural.ofNat": ("ℕ → Supernatural",),
    "Supernatural.profiniteIndex": ("(H : ClosedSubgroup",),
    "Supernatural.profiniteIndex_tower": ("(H N : ClosedSubgroup", "(hNH : N ≤ H)"),
    "Supernatural.torsionOrder_eq_profiniteOrder_pontryagin": (
        "[DiscreteTopology A]", "(hA : IsAddTorsion A)"),
    "Supernatural.torsionOrder_eq_profiniteOrder_character": (
        "[AddCommGroup A]", "(hA : IsAddTorsion A)"),
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


class Header(HTMLParser):
    """Extract visible header text without discarding implicit arguments."""

    def __init__(self, value):
        super().__init__(convert_charrefs=True)
        self.stack = []
        self.text = []
        self.kinds = []
        self.names = []
        self.feed(value)
        self.close()
        require(not self.stack, "unclosed native header")

    def handle_starttag(self, tag, attrs):
        require(tag in {"div", "span", "a"}, "unexpected native header tag")
        attributes = dict(attrs)
        require(len(attrs) == len(attributes), "duplicate native header attribute")
        require(set(attributes) <= {"class", "href"}, "active/unknown header attribute")
        require(tag == "a" or "href" not in attributes, "unexpected header link")
        require("href" not in attributes or not re.match(r"(?i)\s*(?:javascript|data):", attributes["href"]),
                "active header link")
        classes = set(attributes.get("class", "").split())
        if tag == "div" and "decl_type" in classes:
            self.text.append(" ")
        self.stack.append((tag, classes))

    def handle_endtag(self, tag):
        require(bool(self.stack) and self.stack[-1][0] == tag, "unbalanced native header")
        self.stack.pop()

    def handle_data(self, value):
        require(bool(self.stack) or not value.strip(), "text outside native header")
        self.text.append(value)
        if any("decl_kind" in classes for _, classes in self.stack):
            self.kinds.append(value)
        if any("decl_name" in classes for _, classes in self.stack):
            self.names.append(value)

    def handle_comment(self, _):
        raise ValueError("unexpected native header comment")

    def handle_decl(self, _):
        raise ValueError("unexpected native header declaration")

    def rendered(self):
        return " ".join("".join(self.text).split())


def check_snapshot(revision, sources):
    require(revision == SOURCE, "unexpected/stale source revision")
    require(set(sources) == set(INPUTS) == set(INPUT_SHA256), "source/pin inventory differs")
    for path in INPUTS:
        require(digest(sources[path]) == INPUT_SHA256[path], "source/pin drift: " + path)


def source_range(info, raw):
    lines = raw.decode("utf-8").splitlines()
    start = info["line"]
    name = info["name"]
    require(type(start) is int and 0 < start <= len(lines), "invalid native source line: " + name)
    if name == GENERATED:
        require(start == 38 and lines[start - 1].startswith("@[ext]")
                and "attribute [inherit_doc Supernatural.ext] Supernatural.ext_iff" in raw.decode(),
                "generated ext_iff source/inheritance mismatch")
        require(info["doc"].strip() ==
                "Supernatural numbers are equal when their exponents agree at every prime.",
                "generated ext_iff inherited docstring differs")
        return 42, 42, "generated by `@[ext]`; inherited `Supernatural.ext` docstring (line 37)"
    if name == UNDOCUMENTED_INSTANCE:
        require(info["doc"] == "" and
                lines[start - 1].startswith("noncomputable instance : CompleteLattice Supernatural"),
                "anonymous instance line/missing-doc status differs")
    else:
        require(lines[start - 1].startswith("/--"), "native line is not authored docstring: " + name)
        remainder = "\n".join(lines[start - 1:])
        source_doc, closing, after = remainder.partition("-/")
        require(bool(closing) and source_doc[3:].strip() == info["doc"].strip(),
                "native docstring/source mismatch: " + name)
        short = name.rsplit(".", 1)[-1]
        declaration = re.search(r"^\s*(?:noncomputable\s+)?(?:theorem|def|abbrev)\s+" +
                                re.escape(short) + r"\b", after, re.MULTILINE)
        require(declaration is not None and "/--" not in after[:declaration.start()],
                "native docstring/name association differs: " + name)
    end = len(lines)
    for index in range(start, len(lines)):
        if lines[index].startswith(("/--", "end ", "#lint")):
            end = index
            break
    while end > start and not lines[end - 1].strip():
        end -= 1
    require(end >= start, "invalid source range: " + name)
    origin = "original catalogue explanation; no authored docstring" if name == UNDOCUMENTED_INSTANCE else "authored docstring"
    return start, end, origin


def read_records(native_data):
    raw_records = {}
    records = {}
    for module in MODULES:
        raw = (native_data / ("declaration-data-" + module + ".bmp")).read_bytes()
        raw_records[module] = raw
        records[module] = json.loads(raw)
    return records, raw_records


def render(records, revision, sources, raw_records, expected_native_hashes=NATIVE_SHA256):
    check_snapshot(revision, sources)
    require(set(records) == set(raw_records) == set(MODULES) == set(expected_native_hashes),
            "native shipped-module inventory differs")
    entries = []
    registry = {}
    seen = set()
    for module, count in zip(MODULES, COUNTS):
        record = records[module]
        raw = raw_records[module]
        require(json.loads(raw) == record, "native raw record/parsed JSON differs: " + module)
        require(type(record) is dict and set(record) == {"name", "imports", "instances", "declarations"},
                "unsupported native record schema: " + module)
        require(record["name"] == module, "wrong native module: " + module)
        path = module.replace(".", "/") + ".lean"
        imports = set(re.findall(r"^(?:public )?import (\S+)$", sources[path].decode(), re.MULTILINE))
        require(type(record["imports"]) is list and len(record["imports"]) == len(set(record["imports"]))
                and set(record["imports"]) == imports | {"Init"}, "native import graph differs: " + module)
        rows = record["declarations"]
        require(type(rows) is list and len(rows) == count, "native declaration count differs: " + module)
        instances = record["instances"]
        expected_instances = ([{"className": "CompleteLattice", "name": UNDOCUMENTED_INSTANCE,
                               "typeNames": ["Supernatural"]}] if module == MODULES[0] else [])
        require(type(instances) is list and instances == expected_instances,
                "native instance registry differs: " + module)
        registry[module] = instances
        for row in rows:
            require(type(row) is dict and set(row) == {"header", "info"}, "native declaration schema differs")
            info = row["info"]
            require(type(info) is dict and set(info) == {"doc", "docLink", "kind", "line", "name", "sourceLink"},
                    "native declaration info schema differs")
            name = info["name"]
            require(type(name) is str and re.fullmatch(r"[A-Za-z][A-Za-z0-9_.]*", name) and name not in seen,
                    "missing/duplicate/invalid native name: " + str(name))
            seen.add(name)
            require(name.startswith("SupernaturalNumbersTests.") if module == MODULES[6]
                    else name == "Supernatural" or name.startswith("Supernatural."),
                    "native namespace differs: " + name)
            require(type(info["doc"]) is str and type(row["header"]) is str,
                    "native doc/header type differs: " + name)
            require(info["sourceLink"] == f"https://example.invalid/commit/{SOURCE}/{path}",
                    "native source revision/path differs: " + name)
            require(info["docLink"] == f"./{module.replace('.', '/')}.html#{name}",
                    "native docLink identity differs: " + name)
            kind = info["kind"]
            require(kind in {"theorem", "def", "instance"} and
                    (kind == "instance") == (name == UNDOCUMENTED_INSTANCE), "wrong native kind: " + name)
            header = Header(row["header"])
            native_kind = "".join(header.kinds).strip()
            display = header.rendered()
            require("".join(header.names) == name and native_kind in {
                "theorem", "def", "abbrev", "noncomputable def", "noncomputable instance"}
                and ((native_kind.endswith("def") or native_kind == "abbrev") == (kind == "def"))
                and display.startswith(native_kind + " " + name) and "```" not in display,
                "native header identity/kind/signature differs: " + name)
            for fragment in KEY_SIGNATURES.get(name, ()):
                require(fragment in display, "missing essential signature fragment: " + name + " / " + fragment)
            source_start, source_end, origin = source_range(info, sources[path])
            entries.append(dict(module=module, name=name, kind=kind, native_kind=native_kind,
                                signature=display, signature_sha256=digest(display.encode()),
                                raw_header_sha256=digest(row["header"].encode()), doc=info["doc"].strip(),
                                doc_origin=origin, path=path, native_line=info["line"], source_start=source_start,
                                source_end=source_end))
        require(digest(raw) == expected_native_hashes[module], "native raw record drift: " + module)
    require(len(seen) == 120 and GENERATED in seen and UNDOCUMENTED_INSTANCE in seen,
            "native public catalogue differs")
    entries.sort(key=lambda entry: (MODULES.index(entry["module"]), entry["source_start"], entry["name"]))
    lines = ["# Generated API reference", "",
             "Pinned native doc-gen4 signatures for all 120 native declaration entries in",
             "eight shipped modules: 104 production entries (including generated `ext_iff`",
             "and an undocumented anonymous instance) and 16 publicly named checked-use",
             "client entries (including a definition). Both root modules reexport their leaves",
             "and define no own native entries. This is not the complete private/generated",
             "declaration or stored-proof census; that requires a separate release audit.", "",
             "Signatures retain every *displayed* implicit binder, class and universe label.",
             "Only HTML markup and formatting whitespace are normalized. An instance or",
             "definition signature does not certify its body. Native docstrings are labeled",
             "separately from original catalogue text and inherited/generated documentation.",
             "See [reproduction](README.md), [hashes](api-manifest.json),",
             "and [usage and limitations](../README.md).", ""]
    for module in MODULES:
        heading = "Production API" if module in MODULES[:6] else "Public checked-use clients"
        lines.extend(["## " + heading + ": `" + module + "`", ""])
        module_rows = [entry for entry in entries if entry["module"] == module]
        if not module_rows:
            lines.extend(["Reexport-only module: no own native declaration entries.", ""])
        for entry in module_rows:
            anchor = f"#L{entry['source_start']}-L{entry['source_end']}" if entry["source_end"] != entry["source_start"] else f"#L{entry['source_start']}"
            lines.extend(["### `" + entry["name"] + "`", "", "```lean", entry["signature"], "```", ""])
            if entry["name"] == UNDOCUMENTED_INSTANCE:
                lines.extend([INSTANCE_EXPLANATION, ""])
            elif entry["name"] == GENERATED:
                lines.extend(["Inherited `Supernatural.ext` docstring (not independently authored): " + entry["doc"], ""])
            else:
                lines.extend([entry["doc"], ""])
            lines.extend([f"[Source](../{entry['path']}{anchor}) (lines {entry['source_start']}–{entry['source_end']}; {entry['doc_origin']}).", ""])
    markdown = "\n".join(lines).encode("utf-8")
    manifest = dict(format=1, generator="scripts/generate_api.py", docgen_revision=TOOL,
                    analyzed_input_revision=SOURCE, analyzed_input_tree=SOURCE_TREE,
                    modules=list(MODULES), inputs={path: digest(sources[path]) for path in INPUTS},
                    native_record_sha256={module: digest(raw_records[module]) for module in MODULES},
                    native_instance_registry=registry,
                    declaration_counts={module: count for module, count in zip(MODULES, COUNTS)},
                    entries=[{key: value for key, value in entry.items() if key not in {"signature", "doc"}}
                             for entry in entries],
                    signature_hash_semantics="SHA-256 of UTF-8 displayed text after HTML entity decoding and whitespace collapsing; full text in API.md",
                    raw_header_hash_semantics="SHA-256 of UTF-8 verbatim native header HTML inside each raw record",
                    raw_record_hash_semantics="SHA-256 of verbatim native declaration-data-<module>.bmp bytes, not reserialized JSON",
                    api_sha256=digest(markdown), proof_certification=False, release_acceptance=False)
    return markdown, (json.dumps(manifest, indent=2, sort_keys=True, ensure_ascii=False) + "\n").encode("utf-8")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--native-data", type=Path, required=True, help="pinned fromDb doc-data directory")
    parser.add_argument("--source-revision", required=True, help="fixed historical input label; no Git lookup")
    parser.add_argument("--tool-revision", required=True, help="recorded immutable doc-gen4 revision")
    parser.add_argument("--check", action="store_true", help="compare generated bytes without writing")
    args = parser.parse_args()
    require(args.tool_revision == TOOL, "unexpected/stale doc-gen4 revision")
    root = Path(__file__).resolve().parent.parent
    sources = {path: (root / path).read_bytes() for path in INPUTS}
    check_snapshot(args.source_revision, sources)
    records, raw_records = read_records(args.native_data)
    api, manifest = render(records, args.source_revision, sources, raw_records)
    for name, raw in (("API.md", api), ("api-manifest.json", manifest)):
        target = root / "docs" / name
        if args.check:
            require(target.read_bytes() == raw, "generated file differs: " + name)
        else:
            target.parent.mkdir(exist_ok=True)
            target.write_bytes(raw)
    print(json.dumps(dict(status="matched" if args.check else "generated", production=104,
                          clients=16, api_sha256=digest(api), release_acceptance=False)))


if __name__ == "__main__":
    main()
