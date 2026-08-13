"""Tests for cli — .env parsing, argument validation, exit codes."""

from formal import cli


class TestLoadEnv:
    def _env_at(self, tmp_path, monkeypatch, body):
        monkeypatch.setenv("FORMAL_HOME", str(tmp_path))
        (tmp_path / ".env").write_text(body)

    def test_parses_keys_and_strips_quotes(self, tmp_path, monkeypatch):
        self._env_at(tmp_path, monkeypatch, "A=1\nB=\"two\"\nC='three'\n")
        for key in ("A", "B", "C"):
            monkeypatch.delenv(key, raising=False)
        cli._load_env()
        assert (cli.os.environ["A"], cli.os.environ["B"], cli.os.environ["C"]) == ("1", "two", "three")

    def test_skips_comments_and_blank_lines(self, tmp_path, monkeypatch):
        self._env_at(tmp_path, monkeypatch, "# comment\n\nA=1\nnot-a-pair\n")
        monkeypatch.delenv("A", raising=False)
        cli._load_env()
        assert cli.os.environ["A"] == "1"

    def test_does_not_override_the_real_environment(self, tmp_path, monkeypatch):
        self._env_at(tmp_path, monkeypatch, "A=from-file\n")
        monkeypatch.setenv("A", "from-shell")
        cli._load_env()
        assert cli.os.environ["A"] == "from-shell"

    def test_missing_file_is_not_an_error(self, tmp_path, monkeypatch):
        monkeypatch.setenv("FORMAL_HOME", str(tmp_path))
        cli._load_env()
