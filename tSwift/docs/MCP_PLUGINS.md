# MCP Plugin Development Guide

This guide explains how to create and maintain MCP (Model Context Protocol) plugins.

## Architecture Overview

MCP plugins extend Claude Code's capabilities by providing custom tools. They run as separate processes that communicate via stdio using JSON-RPC 2.0.

```
Claude Code <--JSON-RPC--> MCP Server (Python) <--> External APIs/System
                 (stdio)
```

### Plugin Location

```
.claude/plugins/
├── tab-title/          # Terminal title management
│   └── server.py
└── <your-plugin>/
    └── server.py
```

### Configuration

Plugins are registered in `.mcp.json` at the repo root:

```json
{
  "mcpServers": {
    "my-plugin": {
      "type": "stdio",
      "command": "python3",
      "args": [".claude/plugins/my-plugin/server.py"]
    }
  }
}
```

## Creating a New Plugin

### 1. Basic Structure

Create `.claude/plugins/<name>/server.py`:

```python
#!/usr/bin/env python3
"""MCP server for <description>."""

import json
import sys


def handle_request(request: dict) -> dict | None:
    """Handle a single MCP request."""
    method = request.get("method", "")
    req_id = request.get("id")

    # Required: handle initialize
    if method == "initialize":
        return {
            "jsonrpc": "2.0",
            "id": req_id,
            "result": {
                "protocolVersion": "2024-11-05",
                "capabilities": {"tools": {}},
                "serverInfo": {"name": "my-plugin", "version": "1.0.0"},
            },
        }

    # Optional: handle initialized notification
    if method == "notifications/initialized":
        # Perform startup tasks here
        return None  # No response for notifications

    # Required: list available tools
    if method == "tools/list":
        return {
            "jsonrpc": "2.0",
            "id": req_id,
            "result": {
                "tools": [
                    {
                        "name": "my_tool",
                        "description": "What this tool does",
                        "inputSchema": {
                            "type": "object",
                            "properties": {
                                "param1": {
                                    "type": "string",
                                    "description": "Parameter description",
                                },
                            },
                            "required": ["param1"],
                        },
                    },
                ],
            },
        }

    # Handle tool calls
    if method == "tools/call":
        params = request.get("params", {})
        tool_name = params.get("name")
        args = params.get("arguments", {})

        if tool_name == "my_tool":
            try:
                result = do_something(args["param1"])
                return {
                    "jsonrpc": "2.0",
                    "id": req_id,
                    "result": {
                        "content": [{"type": "text", "text": result}],
                    },
                }
            except Exception as e:
                return {
                    "jsonrpc": "2.0",
                    "id": req_id,
                    "result": {
                        "content": [{"type": "text", "text": f"Error: {e}"}],
                        "isError": True,
                    },
                }

    # Unknown method
    return {
        "jsonrpc": "2.0",
        "id": req_id,
        "error": {"code": -32601, "message": f"Unknown method: {method}"},
    }


def main():
    """Main loop - read JSON-RPC from stdin, write to stdout."""
    for line in sys.stdin:
        line = line.strip()
        if not line:
            continue

        try:
            request = json.loads(line)
            response = handle_request(request)
            if response is not None:
                print(json.dumps(response), flush=True)
        except json.JSONDecodeError as e:
            print(
                json.dumps({
                    "jsonrpc": "2.0",
                    "id": None,
                    "error": {"code": -32700, "message": f"Parse error: {e}"},
                }),
                flush=True,
            )


if __name__ == "__main__":
    main()
```

### 2. Register in .mcp.json

Add your plugin to the configuration file.

### 3. Test

Restart Claude Code to load the new plugin. The tools will be available immediately.

## Existing Plugins

### tab-title

**Purpose:** Terminal tab title management for session identification.

**Key tool:**
| Tool | Description |
|------|-------------|
| `set_tab_title` | Set terminal tab title, auto-generates from role+project if not specified |

**Behavior:**
- Auto-sets title on MCP initialization (`notifications/initialized`)
- Uses AppleScript for iTerm2, escape sequences as fallback
- Format: `[W]project` for workers, `[M]project` for managers

**Source:** `.claude/plugins/tab-title/server.py`

## Testing Plugins

### Manual Testing

Send JSON-RPC messages directly:

```bash
echo '{"jsonrpc":"2.0","id":1,"method":"initialize"}' | python3 .claude/plugins/my-plugin/server.py
```

### Integration Testing

Create tests in `tests/test_<plugin>.py`.

## Protocol Reference

MCP uses JSON-RPC 2.0 over stdio. Key message types:

| Method | Direction | Purpose |
|--------|-----------|---------|
| `initialize` | Client→Server | Start session, negotiate capabilities |
| `notifications/initialized` | Client→Server | Session ready, run startup tasks |
| `tools/list` | Client→Server | Get available tools |
| `tools/call` | Client→Server | Execute a tool |

Full protocol: https://modelcontextprotocol.io/specification
