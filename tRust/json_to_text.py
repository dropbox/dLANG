#!/usr/bin/env python3
"""
Convert Claude's and Codex's stream-json output to human-readable text.
Reads JSON lines from stdin, outputs formatted text to stdout.

Supports:
- Claude CLI: --output-format stream-json
- Codex CLI: --json (JSONL events)

Copyright 2026 Dropbox, Inc.
Created by Andrew Yates
Licensed under the Apache License, Version 2.0
"""

import json
import os
import sys
from datetime import datetime

# Detect if we should use colors (TTY or forced via env)
USE_COLORS = sys.stdout.isatty() or os.environ.get('FORCE_COLOR', '') == '1'

# ANSI color codes (empty strings if no TTY)
if USE_COLORS:
    BLUE = '\033[94m'
    GREEN = '\033[92m'
    YELLOW = '\033[93m'
    RED = '\033[91m'
    CYAN = '\033[96m'
    MAGENTA = '\033[95m'
    BOLD = '\033[1m'
    DIM = '\033[2m'
    RESET = '\033[0m'
else:
    BLUE = GREEN = YELLOW = RED = CYAN = MAGENTA = BOLD = DIM = RESET = ''

def timestamp():
    """Get current timestamp for display"""
    return datetime.now().strftime('%H:%M:%S')

def clean_output(text):
    """Remove system noise from output"""
    if text is None:
        return ''
    lines = text.strip().split('\n')
    filtered = []
    skip_mode = False

    for line in lines:
        # Skip Co-Authored-By
        if 'Co-Authored-By:' in line or '🤖 Generated with' in line:
            continue
        # Skip system reminders
        if '<system-reminder>' in line:
            skip_mode = True
            continue
        if '</system-reminder>' in line:
            skip_mode = False
            continue
        if skip_mode:
            continue
        # Skip malware check reminders
        if 'you should consider whether it would be considered malware' in line.lower():
            continue
        filtered.append(line)

    return '\n'.join(filtered)

def format_tool_output(content, tool_name, is_error=False):
    """Format tool output intelligently"""
    text = clean_output(content)
    if not text.strip():
        return None

    lines = text.split('\n')

    # For errors, show more context
    if is_error:
        preview_lines = lines[:15]
        if len(lines) > 15:
            preview_lines.append(f"{DIM}... ({len(lines) - 15} more lines){RESET}")
        return preview_lines

    # For successful tools, show smart preview
    if tool_name == 'Bash':
        # Show first few lines and last line
        if len(lines) <= 3:
            return lines
        return [lines[0], lines[1],
                f"{DIM}... ({len(lines) - 3} more lines){RESET}",
                lines[-1]]

    if tool_name == 'Read':
        # Just show how many lines read
        return [f"{DIM}({len(lines)} lines read){RESET}"]

    if tool_name in ['Write', 'Edit']:
        # Just confirm success
        return None

    if tool_name in ['Grep', 'Glob']:
        # Show first few matches
        if len(lines) <= 5:
            return lines
        result = lines[:5]
        result.append(f"{DIM}... ({len(lines) - 5} more matches){RESET}")
        return result

    # Generic: show first line
    if len(lines) <= 2:
        return lines
    return [lines[0], f"{DIM}... ({len(lines) - 1} more lines){RESET}"]

class MessageFormatter:
    def __init__(self):
        self.last_was_text = False

    def format_text_message(self, text):
        """Format Claude's main messages"""
        if not text.strip():
            return

        # Add spacing if last output was also text
        if self.last_was_text:
            print()

        # Clean up the text
        text = text.strip()

        # Split into paragraphs
        paragraphs = text.split('\n\n')

        for i, para in enumerate(paragraphs):
            para = para.strip()
            if not para:
                continue

            # First paragraph gets timestamp and icon
            if i == 0:
                print(f"\n{DIM}[{timestamp()}]{RESET} {BOLD}{BLUE}💬{RESET} {para}")
            else:
                # Subsequent paragraphs are indented slightly
                print(f"   {para}")

        self.last_was_text = True

    def format_tool_use(self, tool_name, input_data, tool_result=None):
        """Format a tool call with its result"""
        # Handle None input_data
        if input_data is None:
            input_data = {}

        # Build tool description
        if tool_name == 'Read':
            path = input_data.get('file_path', '')
            desc = f"read: {path}"

        elif tool_name == 'Write':
            path = input_data.get('file_path', '')
            size = len(input_data.get('content', ''))
            desc = f"write: {path} ({size} chars)"

        elif tool_name == 'Edit':
            path = input_data.get('file_path', '')
            desc = f"edit: {path}"

        elif tool_name == 'Bash':
            cmd = input_data.get('command', '')
            # Truncate long commands
            if len(cmd) > 80:
                cmd = cmd[:77] + '...'
            desc = f"bash: {cmd}"

        elif tool_name == 'Grep':
            pattern = input_data.get('pattern', '')
            path = input_data.get('path', '.')
            desc = f"grep: '{pattern}' in {path}"

        elif tool_name == 'Glob':
            pattern = input_data.get('pattern', '')
            desc = f"glob: {pattern}"

        elif tool_name == 'TodoWrite':
            todos = input_data.get('todos', [])
            desc = f"todo: update ({len(todos)} items)"

        elif tool_name == 'Task':
            subagent = input_data.get('subagent_type', 'agent')
            task_desc = input_data.get('description', '')
            if task_desc:
                desc = f"task: {subagent} → {task_desc}"
            else:
                desc = f"task: spawn {subagent}"

        elif tool_name == 'WebFetch':
            url = input_data.get('url', '')
            # Truncate long URLs
            if len(url) > 60:
                url = url[:57] + '...'
            desc = f"fetch: {url}"

        elif tool_name == 'WebSearch':
            query = input_data.get('query', '')
            desc = f"search: {query[:50]}{'...' if len(query) > 50 else ''}"

        elif tool_name == 'LSP':
            operation = input_data.get('operation', '')
            filepath = input_data.get('filePath', '')
            desc = f"lsp: {operation} in {filepath}"

        else:
            desc = f"{tool_name.lower()}"

        # Check if result is an error (be specific to avoid false positives)
        is_error = False
        if tool_result:
            result_lower = tool_result.lower()
            # Check for explicit error markers, not just substring presence
            error_patterns = [
                'error:',           # Error: message
                'error -',          # Error - message
                'failed:',          # Failed: message
                'command failed',   # Command failed
                'exit code',        # Non-zero exit code
                'permission denied',
                'no such file',
                'not found',
                'traceback',        # Python traceback
                'exception:',       # Exception: message
                '"is_error": true', # JSON error flag
                '"is_error":true',
            ]
            is_error = any(pattern in result_lower for pattern in error_patterns)

        # Format output
        if is_error:
            # Errors are prominent
            print(f"\n  {RED}✗{RESET} {desc}")
            if tool_result:
                output_lines = format_tool_output(tool_result, tool_name, is_error=True)
                if output_lines:
                    for line in output_lines:
                        print(f"    {RED}{line}{RESET}")
        else:
            # Success - show tool and smart preview
            print(f"  {DIM}•{RESET} {desc}")
            if tool_result:
                output_lines = format_tool_output(tool_result, tool_name, is_error=False)
                if output_lines:
                    for line in output_lines:
                        print(f"    {DIM}→{RESET} {line}")

        self.last_was_text = False

    def format_thinking(self, thinking_text):
        """Format thinking blocks (minimal)"""
        if thinking_text and len(thinking_text) > 100:
            # Only show if substantial thinking
            char_count = len(thinking_text)
            print(f"  {DIM}💭 thinking... ({char_count} chars){RESET}")
            self.last_was_text = False

formatter = MessageFormatter()

# Track tool uses and their results
# Limited to prevent memory leaks from interrupted sessions
MAX_PENDING_TOOLS = 100
pending_tool_uses = {}

def clear_pending_tools():
    """Clear pending tools at session boundaries"""
    global pending_tool_uses
    pending_tool_uses = {}


# =============================================================================
# Codex JSONL Format Handler
# =============================================================================

class CodexFormatter:
    """Format Codex CLI --json JSONL events"""

    def __init__(self):
        self.last_was_text = False
        self.in_session = False

    def format_agent_message(self, item):
        """Format agent text messages"""
        # Codex uses 'text' field in newer versions, 'content' in older
        content = item.get('text', item.get('content', ''))
        if not content or not content.strip():
            return

        text = clean_output(content)
        if not text.strip():
            return

        paragraphs = text.split('\n\n')
        for i, para in enumerate(paragraphs):
            para = para.strip()
            if not para:
                continue
            if i == 0:
                print(f"\n{DIM}[{timestamp()}]{RESET} {BOLD}{BLUE}💬{RESET} {para}")
            else:
                print(f"   {para}")

        self.last_was_text = True

    def format_command_execution(self, item, status='completed'):
        """Format shell command executions"""
        command = item.get('command', '')
        exit_code = item.get('exit_code')
        output = item.get('aggregated_output', '')

        # Truncate long commands
        cmd_display = command
        if len(cmd_display) > 80:
            cmd_display = cmd_display[:77] + '...'

        is_error = exit_code is not None and exit_code != 0

        if is_error:
            print(f"\n  {RED}✗{RESET} bash: {cmd_display} (exit {exit_code})")
            if output:
                lines = output.strip().split('\n')[:10]
                for line in lines:
                    print(f"    {RED}{line}{RESET}")
        else:
            print(f"  {DIM}•{RESET} bash: {cmd_display}")
            if output and status == 'completed':
                lines = output.strip().split('\n')
                if len(lines) <= 3:
                    for line in lines:
                        print(f"    {DIM}→{RESET} {line}")
                else:
                    print(f"    {DIM}→{RESET} {lines[0]}")
                    print(f"    {DIM}... ({len(lines) - 2} more lines){RESET}")
                    print(f"    {DIM}→{RESET} {lines[-1]}")

        self.last_was_text = False

    def format_file_change(self, item):
        """Format file operations"""
        filepath = item.get('file_path', item.get('path', ''))
        change_type = item.get('change_type', 'modify')

        if change_type == 'create':
            print(f"  {DIM}•{RESET} write: {filepath}")
        elif change_type == 'delete':
            print(f"  {DIM}•{RESET} delete: {filepath}")
        else:
            print(f"  {DIM}•{RESET} edit: {filepath}")

        self.last_was_text = False

    def format_reasoning(self, item):
        """Format reasoning/thinking blocks"""
        # Codex uses 'text' field in newer versions, 'content' or 'summary' in older
        content = item.get('text', item.get('content', item.get('summary', '')))
        if content and len(content) > 50:
            print(f"  {DIM}💭 thinking... ({len(content)} chars){RESET}")
            self.last_was_text = False

    def format_mcp_tool_call(self, item):
        """Format MCP tool calls"""
        tool_name = item.get('tool_name', item.get('name', 'mcp_tool'))
        print(f"  {DIM}•{RESET} mcp: {tool_name}")
        self.last_was_text = False

    def format_web_search(self, item):
        """Format web search operations"""
        query = item.get('query', '')
        print(f"  {DIM}•{RESET} search: {query[:60]}{'...' if len(query) > 60 else ''}")
        self.last_was_text = False

    def format_todo_list(self, item):
        """Format todo list updates"""
        todos = item.get('todos', [])
        print(f"  {DIM}•{RESET} todo: update ({len(todos)} items)")
        self.last_was_text = False

    def format_error(self, msg):
        """Format error events"""
        error = msg.get('error', {})
        message = error.get('message', str(error)) if isinstance(error, dict) else str(error)
        print(f"\n  {RED}✗ Error: {message}{RESET}")
        self.last_was_text = False


codex_formatter = CodexFormatter()


def process_codex_event(msg):
    """Process a Codex JSONL event"""
    event_type = msg.get('type', '')

    if event_type == 'thread.started':
        thread_id = msg.get('thread_id', '')
        # Clear any pending tools from previous sessions
        clear_pending_tools()
        print(f"\n{BOLD}{MAGENTA}{'═' * 80}{RESET}")
        print(f"{BOLD}{MAGENTA}  🚀  Codex Session Started  {RESET}")
        if thread_id:
            print(f"{DIM}  Thread: {thread_id}{RESET}")
        print(f"{BOLD}{MAGENTA}{'═' * 80}{RESET}")
        codex_formatter.in_session = True
        return

    if event_type == 'turn.started':
        # Turn started - just note it silently
        return

    if event_type == 'turn.completed':
        # Session/turn complete with usage stats
        codex_formatter.in_session = False
        print(f"\n{DIM}{'─' * 80}{RESET}")
        print(f"{BOLD}{GREEN}  ✓  Turn Complete{RESET}")
        # Show usage stats if available
        usage = msg.get('usage', {})
        if usage:
            input_tokens = usage.get('input_tokens', 0)
            output_tokens = usage.get('output_tokens', 0)
            cached_tokens = usage.get('cached_input_tokens', 0)
            print(f"{DIM}  Input: {input_tokens:,} tokens", end='')
            if cached_tokens:
                print(f" (cached: {cached_tokens:,})", end='')
            print(f" | Output: {output_tokens:,} tokens{RESET}")
        print(f"{DIM}{'─' * 80}{RESET}")
        return

    if event_type == 'turn.failed':
        error = msg.get('error', {})
        message = error.get('message', 'Unknown error') if isinstance(error, dict) else str(error)
        print(f"\n{RED}{'─' * 80}{RESET}")
        print(f"{BOLD}{RED}  ✗  Turn Failed: {message}{RESET}")
        print(f"{RED}{'─' * 80}{RESET}")
        return

    if event_type == 'error':
        codex_formatter.format_error(msg)
        return

    # Handle item events
    if event_type in ('item.completed', 'item.started', 'item.updated'):
        item = msg.get('item', {})
        item_type = item.get('type', '')
        status = item.get('status', 'in_progress')

        # Only show completed items (or started for streaming)
        if event_type == 'item.completed' or (event_type == 'item.started' and item_type == 'agent_message'):
            if item_type == 'agent_message':
                codex_formatter.format_agent_message(item)
            elif item_type == 'command_execution':
                codex_formatter.format_command_execution(item, status)
            elif item_type == 'file_change':
                codex_formatter.format_file_change(item)
            elif item_type == 'reasoning':
                codex_formatter.format_reasoning(item)
            elif item_type == 'mcp_tool_call':
                codex_formatter.format_mcp_tool_call(item)
            elif item_type == 'web_search':
                codex_formatter.format_web_search(item)
            elif item_type == 'todo_list':
                codex_formatter.format_todo_list(item)


def is_codex_event(msg):
    """Detect if this is a Codex event vs Claude message"""
    event_type = msg.get('type', '')
    # Codex uses dot-notation event types
    if '.' in event_type:
        return True
    # Codex-specific top-level types
    if event_type in ('error',) and 'item' not in msg and 'message' not in msg:
        return True
    return False


def process_message(msg):
    """Process a single message from the stream"""
    msg_type = msg.get('type')

    # Handle nested message structure
    if 'message' in msg:
        inner_msg = msg['message']
        role = inner_msg.get('role')
        content = inner_msg.get('content', [])
    else:
        role = msg.get('role')
        content = msg.get('content', [])

    if msg_type == 'init':
        # Clear any pending tools from previous sessions
        clear_pending_tools()
        print(f"\n{BOLD}{MAGENTA}{'═' * 80}{RESET}")
        print(f"{BOLD}{MAGENTA}  🚀  Claude Session Started  {RESET}")
        print(f"{BOLD}{MAGENTA}{'═' * 80}{RESET}")
        return

    if msg_type == 'result':
        # Final result with stats
        stats = msg.get('stats', {})
        print(f"\n{DIM}{'─' * 80}{RESET}")
        print(f"{BOLD}{GREEN}  ✓  Session Complete{RESET}")
        if stats:
            input_tokens = stats.get('input_tokens', 0)
            output_tokens = stats.get('output_tokens', 0)
            cache_read = stats.get('cache_read_input_tokens', 0)
            print(f"{DIM}  Input: {input_tokens:,} tokens", end='')
            if cache_read:
                print(f" (cached: {cache_read:,})", end='')
            print(f" | Output: {output_tokens:,} tokens{RESET}")
        print(f"{DIM}{'─' * 80}{RESET}\n")
        return

    # Process content blocks
    if isinstance(content, str):
        content = [{'type': 'text', 'text': content}]

    for block in content:
        block_type = block.get('type')

        if block_type == 'text':
            text = block.get('text', '')
            if role == 'assistant' and text.strip():
                formatter.format_text_message(text)

        elif block_type == 'thinking':
            thinking = block.get('thinking', '')
            formatter.format_thinking(thinking)

        elif block_type == 'tool_use':
            # Store tool use for later pairing with result
            tool_id = block.get('id', '')
            tool_name = block.get('name', '')
            input_data = block.get('input', {})
            # Limit size to prevent memory leaks
            if len(pending_tool_uses) >= MAX_PENDING_TOOLS:
                # Remove oldest entry (first key)
                oldest_key = next(iter(pending_tool_uses))
                del pending_tool_uses[oldest_key]
            pending_tool_uses[tool_id] = {
                'name': tool_name,
                'input': input_data,
            }

        elif block_type == 'tool_result':
            # Match with tool use
            tool_id = block.get('tool_use_id', '')
            content_data = block.get('content', '')

            # Extract text from content
            if isinstance(content_data, list):
                text_parts = [
                    item.get('text', '')
                    for item in content_data
                    if isinstance(item, dict) and item.get('type') == 'text'
                ]
                result_text = '\n'.join(text_parts)
            else:
                result_text = str(content_data)

            # Get the tool use info
            if tool_id in pending_tool_uses:
                tool_info = pending_tool_uses[tool_id]
                formatter.format_tool_use(
                    tool_info['name'],
                    tool_info['input'],
                    result_text,
                )
                del pending_tool_uses[tool_id]
            else:
                # Orphan tool_result - no matching tool_use (stream corruption?)
                print(f"  {DIM}• tool_result (orphan, id={tool_id[:8] if tool_id else '?'}...){RESET}", file=sys.stderr)

def main():
    """Main entry point"""
    try:
        for line in sys.stdin:
            line = line.strip()
            if not line:
                continue

            try:
                msg = json.loads(line)
                # Dispatch to appropriate handler based on format
                if is_codex_event(msg):
                    process_codex_event(msg)
                else:
                    process_message(msg)
                sys.stdout.flush()
            except json.JSONDecodeError:
                # Not valid JSON, might be regular output
                print(line)
                continue

    except KeyboardInterrupt:
        print(f"\n{YELLOW}⚠️  Interrupted{RESET}")
        sys.exit(0)
    except BrokenPipeError:
        # Handle pipe closing gracefully
        sys.exit(0)

if __name__ == '__main__':
    main()
