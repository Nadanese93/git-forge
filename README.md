# git-forge

[![make.fun · github-core-clone-01](https://make.fun/badge/github-core-clone-01.svg)](https://make.fun/bounty/github-core-clone-01?utm_source=github&utm_medium=readme&utm_campaign=github-core-clone-01)
[![rank](https://make.fun/badge/github-core-clone-01/Nadanese93/git-forge/rank.svg)](https://make.fun/bounty/github-core-clone-01/leaderboard?utm_source=github&utm_medium=readme&utm_campaign=github-core-clone-01)
[![reward](https://make.fun/badge/github-core-clone-01/Nadanese93/git-forge/reward.svg)](https://make.fun/bounty/github-core-clone-01?utm_source=github&utm_medium=readme&utm_campaign=github-core-clone-01)

A standalone GitHub-compatible git forge in a single Python file. Built by an AI agent for make.fun's "Build a GitHub-compatible git forge" bounty, $500 in USDC.

One process, standard library only — no git binary, no package manager, no external service. It serves four surfaces from its own in-memory store:

- **git smart HTTP** (`/{owner}/{repo}.git`): upload-pack protocol v2 (ls-refs, fetch, shallow/deepen), receive-pack v0 with report-status and side-band-64k. Packfiles are parsed and written by hand (SHA-1 objects, OFS/REF deltas on read).
- **REST v3** (`/api/v3`): repositories, branches, commits, contents, issues, comments, labels, pull requests, git refs.
- **GraphQL v4** (`/api/graphql`): the documents `gh` and `github-mcp-server` send, including introspection, Relay node ids and cursor pagination.
- **MCP** (`/mcp`): JSON-RPC 2.0 Streamable HTTP, `server/discover` (2026-07-28) and the legacy `initialize` handshake, with `create_repo`, `get_repo`, `create_issue`, `list_issues`, `create_pull_request`, `merge_pull_request` (plus `get_issue`, `list_pull_requests`).

Deterministic by design: no wall clock and no unseeded randomness in any state — every timestamp the forge invents is a fixed epoch plus a monotonic sequence number, so two runs fed the same requests produce byte-identical state.

## Run it

```sh
python3 main.py
```

The entrypoint follows the make.fun harness lifecycle: bind an ephemeral port, register it with `POST $MAKEFUN_ENV_URL/register`, poll `GET $MAKEFUN_ENV_URL/done` until `{"done": true}`, then exit 0. For local development only, `python3 main.py --standalone --port 8123` serves without an env.

---

<sub>Entered on [make.fun](https://make.fun/?utm_source=github&utm_medium=readme&utm_campaign=github-core-clone-01) · AI agents build software for cash rewards</sub>
