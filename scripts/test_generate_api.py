#!/usr/bin/env python3
"""Data-only corruption tests for the bounded native Markdown adapter.

Adapted from the Formal Frontier Root Stability tests, with Beacon's
source-only reproduction correction and Anchor's Ideal Completion recipe.
Synthetic rows reconstructed from checked-in catalogue metadata are not native
provenance; actual eight raw native records must be verified separately.
"""

import copy
import html
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import unittest

import generate_api as api

ROOT = Path(__file__).resolve().parent.parent


def fixture():
    manifest = json.loads((ROOT / "docs/api-manifest.json").read_bytes())
    markdown = (ROOT / "docs/API.md").read_text()
    signatures = dict(re.findall(r"### `([^`]+)`\n\n```lean\n([^\n]+)\n```", markdown))
    sources = {path: (ROOT / path).read_bytes() for path in api.INPUTS}
    records = {}
    for module in api.MODULES:
        path = module.replace(".", "/") + ".lean"
        imports = re.findall(r"^(?:public )?import (\S+)$", sources[path].decode(), re.MULTILINE)
        records[module] = dict(name=module, imports=["Init", *imports], declarations=[],
                               instances=copy.deepcopy(manifest["native_instance_registry"][module]))
    for entry in manifest["entries"]:
        module, name, path = (entry[key] for key in ("module", "name", "path"))
        signature = signatures[name]
        native_kind = entry["native_kind"]
        prefix = native_kind + " " + name
        assert signature.startswith(prefix)
        header = ('<div class="decl_header"><span class="decl_kind">' + native_kind +
                  '</span> <span class="decl_name">' + name +
                  '</span><div class="decl_type">' + html.escape(signature[len(prefix):]) +
                  '</div></div>')
        if name == api.UNDOCUMENTED_INSTANCE:
            doc = ""
        elif name == api.GENERATED:
            doc = "Supernatural numbers are equal when their exponents agree at every prime."
        else:
            lines = sources[path].decode().splitlines()
            doc = "\n".join(lines[entry["native_line"] - 1:]).partition("-/")[0][3:].strip()
        info = dict(name=name, kind=entry["kind"], line=entry["native_line"], doc=doc,
                    sourceLink=f"https://example.invalid/commit/{api.SOURCE}/{path}",
                    docLink=f"./{module.replace('.', '/')}.html#{name}")
        records[module]["declarations"].append(dict(header=header, info=info))
    return records, sources


def run_fixture(records, sources):
    raw = {module: json.dumps(record, ensure_ascii=False).encode() for module, record in records.items()}
    expected = {module: api.digest(data) for module, data in raw.items()}
    return api.render(records, api.SOURCE, sources, raw, expected)


class NegativeControls(unittest.TestCase):
    def setUp(self):
        self.records, self.sources = fixture()

    def assert_rejected(self, phrase):
        with self.assertRaisesRegex(ValueError, phrase):
            run_fixture(self.records, self.sources)

    def test_full_synthetic_inventory_is_not_native_provenance(self):
        markdown, manifest = run_fixture(self.records, self.sources)
        result = json.loads(manifest)
        self.assertEqual(markdown, (ROOT / "docs/API.md").read_bytes())
        self.assertEqual(result["declaration_counts"], dict(zip(api.MODULES, api.COUNTS)))
        self.assertEqual(len(result["entries"]), 120)
        self.assertEqual(result["native_instance_registry"][api.MODULES[0]][0]["className"],
                         "CompleteLattice")
        self.assertNotEqual(result["native_record_sha256"], api.NATIVE_SHA256)

    def test_wrong_module(self):
        self.records[api.MODULES[0]]["name"] = "Other.Basic"
        self.assert_rejected("wrong native module")

    def test_missing_decl(self):
        self.records[api.MODULES[0]]["declarations"].pop()
        self.assert_rejected("native declaration count differs")

    def test_extra_root_decl(self):
        self.records[api.MODULES[5]]["declarations"].append(
            copy.deepcopy(self.records[api.MODULES[0]]["declarations"][0]))
        self.assert_rejected("native declaration count differs")

    def test_duplicate_name(self):
        rows = self.records[api.MODULES[0]]["declarations"]
        rows[1]["info"]["name"] = rows[0]["info"]["name"]
        self.assert_rejected("duplicate/invalid native name")

    def test_wrong_kind(self):
        row = next(row for row in self.records[api.MODULES[0]]["declarations"]
                   if row["info"]["kind"] == "theorem")
        row["info"]["kind"] = "def"
        self.assert_rejected("header identity/kind/signature differs")

    def test_header_loses_implicit_binder(self):
        row = next(row for row in self.records[api.MODULES[0]]["declarations"]
                   if row["info"]["name"] == "Supernatural.exponent_iSup")
        row["header"] = row["header"].replace("{ι : Sort", "(ι : Sort")
        self.assert_rejected("missing essential signature fragment")

    def test_source_link_revision(self):
        self.records[api.MODULES[0]]["declarations"][0]["info"]["sourceLink"] = "https://example.invalid/other"
        self.assert_rejected("native source revision/path differs")

    def test_wrong_doc_link(self):
        self.records[api.MODULES[0]]["declarations"][0]["info"]["docLink"] = "./other.html"
        self.assert_rejected("native docLink identity differs")

    def test_instance_registry_omitted(self):
        self.records[api.MODULES[0]]["instances"] = []
        self.assert_rejected("native instance registry differs")

    def test_instance_uninvented_docstring(self):
        row = next(row for row in self.records[api.MODULES[0]]["declarations"]
                   if row["info"]["name"] == api.UNDOCUMENTED_INSTANCE)
        row["info"]["doc"] = "Invented native docstring"
        self.assert_rejected("anonymous instance line/missing-doc status differs")

    def test_generated_ext_inheritance(self):
        row = next(row for row in self.records[api.MODULES[0]]["declarations"]
                   if row["info"]["name"] == api.GENERATED)
        row["info"]["doc"] = "Invented inheritance"
        self.assert_rejected("generated ext_iff inherited docstring differs")

    def test_docstring_drift(self):
        self.records[api.MODULES[0]]["declarations"][0]["info"]["doc"] = "Changed"
        self.assert_rejected("native docstring/source mismatch")

    def test_pin_drift(self):
        self.sources["lean-toolchain"] = b"leanprover/lean4:unverified\n"
        self.assert_rejected("source/pin drift: lean-toolchain")

    def test_source_drift(self):
        self.sources["SupernaturalNumbers/Basic.lean"] += b"\n"
        self.assert_rejected("source/pin drift: SupernaturalNumbers/Basic.lean")

    def test_missing_input(self):
        self.sources.pop("lake-manifest.json")
        self.assert_rejected("source/pin inventory differs")

    def test_revision_drift(self):
        with self.assertRaisesRegex(ValueError, "unexpected/stale source revision"):
            api.check_snapshot("0" * 40, self.sources)

    def test_raw_bytes_not_normalized_json(self):
        raw = {module: json.dumps(record).encode() for module, record in self.records.items()}
        expected = {module: api.digest(data) for module, data in raw.items()}
        raw[api.MODULES[0]] += b" "
        with self.assertRaisesRegex(ValueError, "native raw record drift"):
            api.render(self.records, api.SOURCE, self.sources, raw, expected)

    def test_active_markup_rejected(self):
        self.records[api.MODULES[0]]["declarations"][0]["header"] += "<script>alert(1)</script>"
        self.assert_rejected("unexpected native header tag")

    def test_optimized_execution_exits_before_writing(self):
        with tempfile.TemporaryDirectory() as temporary:
            result = subprocess.run([sys.executable, "-O", str(ROOT / "scripts/generate_api.py"),
                                     "--native-data", temporary, "--source-revision", api.SOURCE,
                                     "--tool-revision", api.TOOL],
                                    capture_output=True, text=True, cwd=temporary, check=False)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("optimized Python", result.stderr)
            self.assertEqual(list(Path(temporary).iterdir()), [])

    def test_wrong_tool_revision_refused_before_writing(self):
        with tempfile.TemporaryDirectory() as temporary:
            result = subprocess.run([sys.executable, "-B", str(ROOT / "scripts/generate_api.py"),
                                     "--native-data", temporary, "--source-revision", api.SOURCE,
                                     "--tool-revision", "0" * 40],
                                    capture_output=True, text=True, cwd=temporary, check=False)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("unexpected/stale doc-gen4 revision", result.stderr)
            self.assertEqual(list(Path(temporary).iterdir()), [])

    def test_source_only_without_git_object(self):
        api.check_snapshot(api.SOURCE, self.sources)
        self.assertEqual({path: api.digest(raw) for path, raw in self.sources.items()},
                         api.INPUT_SHA256)


if __name__ == "__main__":
    unittest.main()
