"""Tests for server lifecycle resolution.

Starting the server has to be safe to run unconditionally — an agent cannot see
the machine's process list, so `start` is expected to be a no-op when something
is already answering, and `stop` must refuse to signal a pid it does not own.
"""

from unittest.mock import patch

import pytest

from formal import server


@pytest.fixture(autouse=True)
def isolated_home(tmp_path, monkeypatch):
    monkeypatch.setattr(server, "FORMAL_HOME", tmp_path)


class TestResolution:
    def test_defaults(self, monkeypatch):
        monkeypatch.delenv("FORMAL_HOST", raising=False)
        monkeypatch.delenv("FORMAL_PORT", raising=False)
        assert server.host() == "127.0.0.1"
        assert server.port() == 1337

    def test_env_overrides(self, monkeypatch):
        monkeypatch.setenv("FORMAL_HOST", "0.0.0.0")
        monkeypatch.setenv("FORMAL_PORT", "9001")
        assert server.base_url() == "http://0.0.0.0:9001"

    def test_a_blank_value_falls_back(self, monkeypatch):
        monkeypatch.setenv("FORMAL_HOST", "   ")
        monkeypatch.setenv("FORMAL_PORT", "")
        assert server.base_url() == "http://127.0.0.1:1337"

    def test_an_unparseable_port_falls_back(self, monkeypatch):
        """A typo in .env should not take the server down with a ValueError."""
        monkeypatch.setenv("FORMAL_PORT", "thirteen-thirty-seven")
        assert server.port() == 1337

    def test_explicit_arguments_win(self):
        assert server.base_url("10.0.0.1", 8080) == "http://10.0.0.1:8080"


class TestIsRunning:
    def test_nothing_listening_is_not_running(self):
        assert not server.is_running("127.0.0.1", 1, timeout=0.1)

    def test_a_healthy_response_is_running(self):
        class _Response:
            status = 200

            def __enter__(self):
                return self

            def __exit__(self, *_):
                return False

        with patch("formal.server.urllib.request.urlopen", return_value=_Response()):
            assert server.is_running()


class TestStart:
    def test_an_already_running_server_is_not_started_again(self):
        with (
            patch("formal.server.is_running", return_value=True),
            patch("formal.server.subprocess.Popen") as popen,
        ):
            url = server.start("127.0.0.1", 1337)

        assert popen.call_count == 0
        assert url == "http://127.0.0.1:1337"

    def test_a_server_that_dies_immediately_is_reported(self):
        process = type("P", (), {"pid": 4242, "poll": lambda self: 1, "returncode": 1})()
        with (
            patch("formal.server.is_running", return_value=False),
            patch("formal.server.subprocess.Popen", return_value=process),
            pytest.raises(RuntimeError, match="exited immediately"),
        ):
            server.start("127.0.0.1", 1337, wait=1.0)


class TestStop:
    def test_nothing_recorded_means_nothing_to_stop(self):
        assert not server.stop()

    def test_a_pid_we_do_not_own_is_never_signalled(self):
        """A stale pid file can name a process the OS has since reused."""
        server.pid_file().write_text("4242")
        with (
            patch("formal.server._is_ours", return_value=False),
            patch("formal.server.os.kill") as kill,
        ):
            stopped = server.stop()

        assert not stopped
        assert kill.call_count == 0
        assert not server.pid_file().exists()

    def test_a_vanished_process_clears_the_pid_file(self):
        server.pid_file().write_text("4242")
        with (
            patch("formal.server._is_ours", return_value=True),
            patch("formal.server.os.kill", side_effect=ProcessLookupError),
        ):
            assert not server.stop()
        assert not server.pid_file().exists()

    def test_a_stopped_server_clears_the_pid_file(self):
        server.pid_file().write_text("4242")
        with (
            patch("formal.server._is_ours", return_value=True),
            patch("formal.server.os.kill"),
            patch("formal.server.is_running", return_value=False),
        ):
            assert server.stop()
        assert not server.pid_file().exists()

    def test_a_corrupt_pid_file_is_survivable(self):
        server.pid_file().write_text("not-a-pid")
        assert not server.stop()
