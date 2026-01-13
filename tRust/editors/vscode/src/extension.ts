/**
 * tRust Verification Extension for VS Code
 *
 * Provides inline verification status, diagnostics, and counterexample display
 * by invoking the trustc compiler with JSON output mode.
 */

import * as vscode from 'vscode';
import * as path from 'path';
import * as fs from 'fs';
import { spawn } from 'child_process';

// Diagnostic collection for verification results
let diagnosticCollection: vscode.DiagnosticCollection;

// Decoration types for inline status
let verifiedDecoration: vscode.TextEditorDecorationType;
let disprovenDecoration: vscode.TextEditorDecorationType;
let unknownDecoration: vscode.TextEditorDecorationType;

// Status bar item
let statusBarItem: vscode.StatusBarItem;

// Output channel for verbose logging
let outputChannel: vscode.OutputChannel;

// Store last verification results for CodeLens
let lastVerificationResults: Map<string, TrustJsonReport> = new Map();

// Global CodeLens provider instance
let codeLensProvider: TrustCodeLensProvider;

/**
 * JSON output types matching tRust's json_output.rs
 */
interface TrustJsonReport {
    version: string;
    crate_name: string;
    trust_level: string;
    timestamp: string;
    summary: TrustSummary;
    functions: TrustFunctionResult[];
    overflow_errors: TrustOverflowError[];
    bounds_errors: TrustBoundsError[];
    effect_errors: TrustEffectError[];
    wiring?: TrustWiringReport;
}

interface TrustSummary {
    total_functions: number;
    verified: number;
    disproven: number;
    unknown: number;
    no_specs: number;
    assumed: number;
    overflow_errors: number;
    bounds_errors: number;
    effect_errors: number;
    wiring_errors: number;
}

interface TrustFunctionResult {
    name: string;
    status: 'verified' | 'disproven' | 'unknown' | 'no_specs' | 'assumed';
    specs_count: number;
    message?: string;
    counterexample?: TrustCounterexample;
    location?: TrustLocation;
    function_hash?: string;
    spec_hash?: string;
}

interface TrustCounterexample {
    inputs: Array<{ name: string; value: string }>;
    description: string;
}

interface TrustLocation {
    file: string;
    line: number;
    column: number;
}

interface TrustOverflowError {
    function: string;
    operation: string;
    operand_type: string;
    location: TrustLocation;
    counterexample?: TrustCounterexample;
    suggestion: string;
}

interface TrustBoundsError {
    function: string;
    index: string;
    length: string;
    location: TrustLocation;
    counterexample?: TrustCounterexample;
    suggestion: string;
}

interface TrustEffectError {
    caller: string;
    callee: string;
    missing_effects: string[];
    location: TrustLocation;
    suggestion: string;
}

interface TrustWiringReport {
    errors: Array<{
        kind: string;
        function: string;
        state?: string;
        target_state?: string;
        location?: TrustLocation;
    }>;
}

/**
 * Find the trustc binary by checking multiple locations
 */
function findTrustc(): string | undefined {
    const config = vscode.workspace.getConfiguration('trust');
    const configPath = config.get<string>('trustcPath');

    // Priority 1: User-configured path (trust if set)
    if (configPath && configPath.length > 0) {
        if (fs.existsSync(configPath)) {
            return configPath;
        }
        outputChannel?.appendLine(`Warning: Configured trustc path not found: ${configPath}`);
    }

    // Priority 2: Workspace bin/trustc
    const workspaceFolder = vscode.workspace.workspaceFolders?.[0];
    if (workspaceFolder) {
        const localPath = path.join(workspaceFolder.uri.fsPath, 'bin', 'trustc');
        if (fs.existsSync(localPath)) {
            return localPath;
        }
    }

    // Priority 3: Check common installation paths
    const homedir = process.env.HOME || process.env.USERPROFILE || '';
    const commonPaths = [
        path.join(homedir, 'tRust', 'bin', 'trustc'),
        path.join(homedir, '.local', 'bin', 'trustc'),
        '/usr/local/bin/trustc',
    ];

    for (const p of commonPaths) {
        if (fs.existsSync(p)) {
            return p;
        }
    }

    // Priority 4: Fall back to PATH (let spawn handle resolution)
    return 'trustc';
}

/**
 * Run trustc verification on a file
 */
async function verifyFile(document: vscode.TextDocument): Promise<TrustJsonReport | null> {
    const trustcPath = findTrustc();
    if (!trustcPath) {
        vscode.window.showErrorMessage('trustc not found. Please set trust.trustcPath in settings.');
        return null;
    }

    const config = vscode.workspace.getConfiguration('trust');
    const useGlobalCache = config.get<boolean>('useGlobalCache', false);
    const verbose = config.get<boolean>('verboseOutput', false);

    const args = ['--output-format=json', document.uri.fsPath];
    if (useGlobalCache) {
        args.unshift('--use-global-cache');
    }
    if (verbose) {
        args.unshift('--verify-verbose');
    }

    return new Promise((resolve) => {
        let stdout = '';
        let stderr = '';

        const proc = spawn(trustcPath, args, {
            cwd: vscode.workspace.workspaceFolders?.[0]?.uri.fsPath
        });

        proc.stdout.on('data', (data: Buffer) => {
            stdout += data.toString();
        });

        proc.stderr.on('data', (data: Buffer) => {
            stderr += data.toString();
            if (verbose) {
                outputChannel.append(data.toString());
            }
        });

        proc.on('close', (code) => {
            if (verbose) {
                outputChannel.appendLine(`trustc exited with code ${code}`);
            }

            // Try to parse JSON output
            try {
                // Find the JSON object in stdout (may have other output mixed in)
                const jsonMatch = stdout.match(/\{[\s\S]*\}$/);
                if (jsonMatch) {
                    const report = JSON.parse(jsonMatch[0]) as TrustJsonReport;
                    resolve(report);
                } else {
                    outputChannel.appendLine('No JSON output found in trustc response');
                    resolve(null);
                }
            } catch (e) {
                outputChannel.appendLine(`Failed to parse trustc output: ${e}`);
                outputChannel.appendLine(`stdout: ${stdout}`);
                resolve(null);
            }
        });

        proc.on('error', (err: NodeJS.ErrnoException) => {
            outputChannel.appendLine(`Failed to run trustc: ${err.message}`);
            if (err.code === 'ENOENT') {
                outputChannel.appendLine('trustc not found. Please either:');
                outputChannel.appendLine('  1. Set trust.trustcPath in VS Code settings');
                outputChannel.appendLine('  2. Add trustc to your PATH');
                outputChannel.appendLine('  3. Place trustc in your workspace bin/ directory');
            }
            resolve(null);
        });
    });
}

/**
 * Convert a TrustLocation to a VS Code Range
 */
function locationToRange(loc: TrustLocation): vscode.Range {
    // tRust uses 1-based lines and columns
    const line = Math.max(0, loc.line - 1);
    const column = Math.max(0, loc.column - 1);
    return new vscode.Range(line, column, line, column + 1);
}

function locationToLineEndRange(doc: vscode.TextDocument, loc: TrustLocation): vscode.Range {
    const line = Math.max(0, Math.min(doc.lineCount - 1, loc.line - 1));
    const end = doc.lineAt(line).range.end.character;
    return new vscode.Range(line, end, line, end);
}

/**
 * Process verification results and update diagnostics
 */
function processResults(document: vscode.TextDocument, report: TrustJsonReport): void {
    const diagnostics: vscode.Diagnostic[] = [];

    // Process function results
    for (const func of report.functions) {
        if (func.status === 'disproven' && func.location) {
            const range = locationToRange(func.location);
            const message = func.counterexample
                ? `Contract disproven: ${func.message || 'specification violated'}\nCounterexample: ${func.counterexample.description}`
                : `Contract disproven: ${func.message || 'specification violated'}`;

            const diagnostic = new vscode.Diagnostic(range, message, vscode.DiagnosticSeverity.Error);
            diagnostic.source = 'tRust';
            diagnostic.code = 'E0900';
            diagnostics.push(diagnostic);
        } else if (func.status === 'unknown' && func.location) {
            const range = locationToRange(func.location);
            const diagnostic = new vscode.Diagnostic(
                range,
                `Verification unknown: ${func.message || 'could not determine'}`,
                vscode.DiagnosticSeverity.Warning
            );
            diagnostic.source = 'tRust';
            diagnostics.push(diagnostic);
        }
    }

    // Process overflow errors
    for (const err of report.overflow_errors) {
        const range = locationToRange(err.location);
        let message = `Potential overflow in ${err.operation} (${err.operand_type})`;
        if (err.counterexample) {
            message += `\nCounterexample: ${err.counterexample.description}`;
            if (err.counterexample.inputs.length > 0) {
                message += `\nInputs:\n${err.counterexample.inputs.map((i) => `  ${i.name} = ${i.value}`).join('\n')}`;
            }
        }
        message += `\nSuggestion: ${err.suggestion}`;

        const diagnostic = new vscode.Diagnostic(range, message, vscode.DiagnosticSeverity.Error);
        diagnostic.source = 'tRust';
        diagnostic.code = 'E0906';
        diagnostics.push(diagnostic);
    }

    // Process bounds errors
    for (const err of report.bounds_errors) {
        const range = locationToRange(err.location);
        let message = `Potential array index out of bounds: index=${err.index}, length=${err.length}`;
        if (err.counterexample) {
            message += `\nCounterexample: ${err.counterexample.description}`;
            if (err.counterexample.inputs.length > 0) {
                message += `\nInputs:\n${err.counterexample.inputs.map((i) => `  ${i.name} = ${i.value}`).join('\n')}`;
            }
        }
        message += `\nSuggestion: ${err.suggestion}`;

        const diagnostic = new vscode.Diagnostic(range, message, vscode.DiagnosticSeverity.Error);
        diagnostic.source = 'tRust';
        diagnostic.code = 'E0908';
        diagnostics.push(diagnostic);
    }

    // Process effect errors
    for (const err of report.effect_errors) {
        const range = locationToRange(err.location);
        const message = `Effect violation: ${err.caller} calls ${err.callee} but lacks effects: ${err.missing_effects.join(', ')}\nSuggestion: ${err.suggestion}`;

        const diagnostic = new vscode.Diagnostic(range, message, vscode.DiagnosticSeverity.Error);
        diagnostic.source = 'tRust';
        diagnostics.push(diagnostic);
    }

    // Process wiring errors
    if (report.wiring) {
        for (const err of report.wiring.errors) {
            if (err.location) {
                const range = locationToRange(err.location);
                let message = `Wiring error (${err.kind}): ${err.function}`;
                if (err.state) {
                    message += ` state="${err.state}"`;
                }
                if (err.target_state) {
                    message += ` target="${err.target_state}"`;
                }

                const diagnostic = new vscode.Diagnostic(range, message, vscode.DiagnosticSeverity.Warning);
                diagnostic.source = 'tRust';
                diagnostics.push(diagnostic);
            }
        }
    }

    diagnosticCollection.set(document.uri, diagnostics);
}

/**
 * Update inline decorations for function verification status
 */
function updateDecorations(editor: vscode.TextEditor, report: TrustJsonReport): void {
    const config = vscode.workspace.getConfiguration('trust');
    if (!config.get<boolean>('showInlineStatus', true)) {
        return;
    }

    const verified: vscode.DecorationOptions[] = [];
    const disproven: vscode.DecorationOptions[] = [];
    const unknown: vscode.DecorationOptions[] = [];

    for (const func of report.functions) {
        if (!func.location) continue;

        const range = locationToLineEndRange(editor.document, func.location);
        const decoration: vscode.DecorationOptions = {
            range,
            hoverMessage: new vscode.MarkdownString(getHoverMessage(func))
        };

        switch (func.status) {
            case 'verified':
                verified.push(decoration);
                break;
            case 'disproven':
                disproven.push(decoration);
                break;
            case 'unknown':
                unknown.push(decoration);
                break;
        }
    }

    editor.setDecorations(verifiedDecoration, verified);
    editor.setDecorations(disprovenDecoration, disproven);
    editor.setDecorations(unknownDecoration, unknown);
}

function extractSuggestionFromDiagnosticMessage(message: string): string | null {
    const idx = message.lastIndexOf('\nSuggestion:');
    if (idx === -1) return null;
    return message
        .slice(idx + '\nSuggestion:'.length)
        .trim()
        .replace(/\r/g, '');
}

class TrustCodeActionProvider implements vscode.CodeActionProvider {
    public static readonly providedCodeActionKinds = [vscode.CodeActionKind.QuickFix];

    provideCodeActions(
        document: vscode.TextDocument,
        _range: vscode.Range,
        context: vscode.CodeActionContext
    ): vscode.CodeAction[] {
        const actions: vscode.CodeAction[] = [];

        for (const diagnostic of context.diagnostics) {
            if (diagnostic.source !== 'tRust') continue;

            // Add "Open explain" action for E09xx error codes
            const errorCode = diagnostic.code;
            if (typeof errorCode === 'string' && /^E09\d{2}$/.test(errorCode)) {
                const explainAction = new vscode.CodeAction(
                    `tRust: Show explanation for ${errorCode}`,
                    vscode.CodeActionKind.QuickFix
                );
                explainAction.diagnostics = [diagnostic];
                explainAction.command = {
                    command: 'trust.explainError',
                    title: `Explain ${errorCode}`,
                    arguments: [errorCode]
                };
                explainAction.isPreferred = false;
                actions.push(explainAction);
            }

            const suggestion = extractSuggestionFromDiagnosticMessage(diagnostic.message);
            if (!suggestion) continue;

            const shortSuggestion = suggestion.length > 80 ? `${suggestion.slice(0, 77)}...` : suggestion;
            const line = diagnostic.range.start.line;
            const lineText = document.lineAt(line).text;
            const indent = lineText.match(/^\s*/)?.[0] ?? '';

            const insertAction = new vscode.CodeAction(
                `tRust: Insert suggestion comment (${shortSuggestion})`,
                vscode.CodeActionKind.QuickFix
            );
            insertAction.diagnostics = [diagnostic];

            const prevLine = line > 0 ? document.lineAt(line - 1).text : '';
            if (!prevLine.includes('tRust suggestion:') || !prevLine.includes(suggestion)) {
                const edit = new vscode.WorkspaceEdit();
                edit.insert(
                    document.uri,
                    new vscode.Position(line, 0),
                    `${indent}// tRust suggestion: ${suggestion}\n`
                );
                insertAction.edit = edit;
                actions.push(insertAction);
            }

            const copyAction = new vscode.CodeAction(
                `tRust: Copy suggestion (${shortSuggestion})`,
                vscode.CodeActionKind.QuickFix
            );
            copyAction.diagnostics = [diagnostic];
            copyAction.command = {
                command: 'trust.copySuggestion',
                title: 'Copy suggestion',
                arguments: [suggestion]
            };
            actions.push(copyAction);
        }

        return actions;
    }
}

/**
 * CodeLens provider that shows verification status above function definitions
 */
class TrustCodeLensProvider implements vscode.CodeLensProvider {
    private _onDidChangeCodeLenses: vscode.EventEmitter<void> = new vscode.EventEmitter<void>();
    public readonly onDidChangeCodeLenses: vscode.Event<void> = this._onDidChangeCodeLenses.event;

    /**
     * Refresh CodeLenses when verification results change
     */
    public refresh(): void {
        this._onDidChangeCodeLenses.fire();
    }

    provideCodeLenses(document: vscode.TextDocument): vscode.CodeLens[] {
        const lenses: vscode.CodeLens[] = [];

        // Check if CodeLens is enabled in configuration
        const config = vscode.workspace.getConfiguration('trust');
        if (!config.get<boolean>('showCodeLens', true)) {
            return lenses;
        }

        const filePath = document.uri.fsPath;
        const report = lastVerificationResults.get(filePath);

        if (!report) {
            return lenses;
        }

        for (const func of report.functions) {
            if (!func.location) continue;

            // Create range for the function definition line
            const line = Math.max(0, func.location.line - 1);
            const range = new vscode.Range(line, 0, line, 0);

            // Determine status icon and label
            let title: string;
            let command: vscode.Command | undefined;

            switch (func.status) {
                case 'verified':
                    title = `✓ PROVEN${func.specs_count > 0 ? ` (${func.specs_count} specs)` : ''}`;
                    command = {
                        title,
                        command: 'trust.showFunctionDetails',
                        arguments: [func]
                    };
                    break;
                case 'disproven':
                    title = `✗ DISPROVEN${func.counterexample ? ' - counterexample found' : ''}`;
                    command = {
                        title,
                        command: 'trust.showFunctionDetails',
                        arguments: [func]
                    };
                    break;
                case 'unknown':
                    title = '? UNKNOWN - could not determine';
                    command = {
                        title,
                        command: 'trust.showFunctionDetails',
                        arguments: [func]
                    };
                    break;
                case 'assumed':
                    title = '⊘ ASSUMED (trust_level)';
                    command = {
                        title,
                        command: ''
                    };
                    break;
                case 'no_specs':
                    title = '○ (no specs)';
                    command = {
                        title,
                        command: ''
                    };
                    break;
                default:
                    continue;
            }

            const lens = new vscode.CodeLens(range, command);
            lenses.push(lens);
        }

        return lenses;
    }
}

/**
 * Generate hover message for a function result
 */
function getHoverMessage(func: TrustFunctionResult): string {
    let msg = `**${func.name}**: ${func.status}`;

    if (func.specs_count > 0) {
        msg += ` (${func.specs_count} specs)`;
    }

    if (func.message) {
        msg += `\n\n${func.message}`;
    }

    if (func.counterexample) {
        msg += `\n\n**Counterexample:** ${func.counterexample.description}`;
        if (func.counterexample.inputs.length > 0) {
            msg += '\n\n```\n';
            for (const input of func.counterexample.inputs) {
                msg += `${input.name} = ${input.value}\n`;
            }
            msg += '```';
        }
    }

    if (func.spec_hash) {
        msg += `\n\n*spec_hash: ${func.spec_hash.substring(0, 16)}...*`;
    }

    return msg;
}

/**
 * Update status bar with verification summary
 */
function updateStatusBar(report: TrustJsonReport): void {
    const s = report.summary;
    const total = s.total_functions;
    const issues = s.disproven + s.overflow_errors + s.bounds_errors + s.effect_errors;

    if (issues > 0) {
        statusBarItem.text = `$(error) tRust: ${s.verified}/${total} verified, ${issues} issues`;
        statusBarItem.backgroundColor = new vscode.ThemeColor('statusBarItem.errorBackground');
    } else if (s.unknown > 0) {
        statusBarItem.text = `$(warning) tRust: ${s.verified}/${total} verified, ${s.unknown} unknown`;
        statusBarItem.backgroundColor = new vscode.ThemeColor('statusBarItem.warningBackground');
    } else {
        statusBarItem.text = `$(check) tRust: ${s.verified}/${total} verified`;
        statusBarItem.backgroundColor = undefined;
    }

    statusBarItem.show();
}

/**
 * Verify command handler
 */
async function verifyCommand(): Promise<void> {
    const editor = vscode.window.activeTextEditor;
    if (!editor || editor.document.languageId !== 'rust') {
        vscode.window.showWarningMessage('tRust: Please open a Rust file to verify');
        return;
    }

    statusBarItem.text = '$(sync~spin) tRust: Verifying...';
    statusBarItem.show();

    const report = await verifyFile(editor.document);
    if (report) {
        // Store results for CodeLens
        lastVerificationResults.set(editor.document.uri.fsPath, report);

        processResults(editor.document, report);
        updateDecorations(editor, report);
        updateStatusBar(report);

        // Refresh CodeLens
        codeLensProvider?.refresh();

        const s = report.summary;
        const issues = s.disproven + s.overflow_errors + s.bounds_errors;
        if (issues === 0 && s.unknown === 0) {
            vscode.window.showInformationMessage(`tRust: ${s.verified}/${s.total_functions} functions verified`);
        }
    } else {
        statusBarItem.text = '$(error) tRust: Verification failed';
    }
}

/**
 * Aggregate summary for workspace verification
 */
interface WorkspaceSummary {
    filesProcessed: number;
    filesWithErrors: number;
    totalFunctions: number;
    verified: number;
    disproven: number;
    unknown: number;
    noSpecs: number;
    assumed: number;
    overflowErrors: number;
    boundsErrors: number;
    effectErrors: number;
}

/**
 * Verify workspace command handler - verifies all Rust files in the workspace
 */
async function verifyWorkspaceCommand(): Promise<void> {
    const workspaceFolders = vscode.workspace.workspaceFolders;
    if (!workspaceFolders || workspaceFolders.length === 0) {
        vscode.window.showWarningMessage('tRust: No workspace folder open');
        return;
    }

    // Find all Rust files in the workspace
    const rustFiles = await vscode.workspace.findFiles('**/*.rs', '**/target/**');
    if (rustFiles.length === 0) {
        vscode.window.showInformationMessage('tRust: No Rust files found in workspace');
        return;
    }

    outputChannel.show();
    outputChannel.appendLine(`=== Workspace Verification Started ===`);
    outputChannel.appendLine(`Found ${rustFiles.length} Rust file(s) to verify\n`);

    // Initialize aggregate summary
    const summary: WorkspaceSummary = {
        filesProcessed: 0,
        filesWithErrors: 0,
        totalFunctions: 0,
        verified: 0,
        disproven: 0,
        unknown: 0,
        noSpecs: 0,
        assumed: 0,
        overflowErrors: 0,
        boundsErrors: 0,
        effectErrors: 0
    };

    // Use progress indicator
    await vscode.window.withProgress(
        {
            location: vscode.ProgressLocation.Notification,
            title: 'tRust: Verifying workspace',
            cancellable: true
        },
        async (progress, token) => {
            const fileCount = rustFiles.length;
            let processedCount = 0;

            for (const fileUri of rustFiles) {
                if (token.isCancellationRequested) {
                    outputChannel.appendLine('\n=== Verification Cancelled ===');
                    return;
                }

                const relativePath = vscode.workspace.asRelativePath(fileUri);
                progress.report({
                    message: `(${processedCount + 1}/${fileCount}) ${relativePath}`,
                    increment: (1 / fileCount) * 100
                });

                outputChannel.appendLine(`Verifying: ${relativePath}`);

                try {
                    const document = await vscode.workspace.openTextDocument(fileUri);
                    const report = await verifyFile(document);

                    if (report) {
                        // Aggregate results
                        summary.filesProcessed++;
                        summary.totalFunctions += report.summary.total_functions;
                        summary.verified += report.summary.verified;
                        summary.disproven += report.summary.disproven;
                        summary.unknown += report.summary.unknown;
                        summary.noSpecs += report.summary.no_specs;
                        summary.assumed += report.summary.assumed;
                        summary.overflowErrors += report.summary.overflow_errors;
                        summary.boundsErrors += report.summary.bounds_errors;
                        summary.effectErrors += report.summary.effect_errors;

                        // Track files with errors
                        const hasErrors = report.summary.disproven > 0 ||
                            report.summary.overflow_errors > 0 ||
                            report.summary.bounds_errors > 0 ||
                            report.summary.effect_errors > 0;
                        if (hasErrors) {
                            summary.filesWithErrors++;
                        }

                        // Store results for CodeLens
                        lastVerificationResults.set(document.uri.fsPath, report);

                        // Update diagnostics for this file
                        processResults(document, report);

                        // Log file summary
                        const fileStatus = hasErrors ? '✗ ISSUES' :
                            report.summary.unknown > 0 ? '? UNKNOWN' : '✓ OK';
                        outputChannel.appendLine(
                            `  ${fileStatus}: ${report.summary.verified}/${report.summary.total_functions} verified`
                        );
                    } else {
                        outputChannel.appendLine(`  ⚠ Failed to verify (no JSON output)`);
                    }
                } catch (err) {
                    outputChannel.appendLine(`  ✗ Error: ${err}`);
                }

                processedCount++;
            }

            // Output final summary
            outputChannel.appendLine(`\n=== Workspace Verification Complete ===`);
            outputChannel.appendLine(`Files: ${summary.filesProcessed}/${fileCount} processed`);
            outputChannel.appendLine(`Files with errors: ${summary.filesWithErrors}`);
            outputChannel.appendLine(`Functions: ${summary.totalFunctions} total`);
            outputChannel.appendLine(`  Verified: ${summary.verified}`);
            outputChannel.appendLine(`  Disproven: ${summary.disproven}`);
            outputChannel.appendLine(`  Unknown: ${summary.unknown}`);
            outputChannel.appendLine(`  No specs: ${summary.noSpecs}`);
            outputChannel.appendLine(`  Assumed: ${summary.assumed}`);
            outputChannel.appendLine(`Overflow errors: ${summary.overflowErrors}`);
            outputChannel.appendLine(`Bounds errors: ${summary.boundsErrors}`);
            outputChannel.appendLine(`Effect errors: ${summary.effectErrors}`);

            // Update status bar with workspace summary
            const totalIssues = summary.disproven + summary.overflowErrors +
                summary.boundsErrors + summary.effectErrors;
            if (totalIssues > 0) {
                statusBarItem.text = `$(error) tRust: ${summary.verified}/${summary.totalFunctions} verified, ${totalIssues} issues`;
                statusBarItem.backgroundColor = new vscode.ThemeColor('statusBarItem.errorBackground');
            } else if (summary.unknown > 0) {
                statusBarItem.text = `$(warning) tRust: ${summary.verified}/${summary.totalFunctions} verified, ${summary.unknown} unknown`;
                statusBarItem.backgroundColor = new vscode.ThemeColor('statusBarItem.warningBackground');
            } else {
                statusBarItem.text = `$(check) tRust: ${summary.verified}/${summary.totalFunctions} verified`;
                statusBarItem.backgroundColor = undefined;
            }
            statusBarItem.show();

            // Refresh CodeLens for all verified files
            codeLensProvider?.refresh();

            // Show completion message
            if (totalIssues > 0) {
                vscode.window.showWarningMessage(
                    `tRust: ${summary.filesWithErrors}/${summary.filesProcessed} file(s) have verification issues`
                );
            } else {
                vscode.window.showInformationMessage(
                    `tRust: Workspace verified - ${summary.verified}/${summary.totalFunctions} functions OK`
                );
            }
        }
    );
}

/**
 * Extension activation
 */
export function activate(context: vscode.ExtensionContext): void {
    // Create diagnostic collection
    diagnosticCollection = vscode.languages.createDiagnosticCollection('trust');
    context.subscriptions.push(diagnosticCollection);

    // Create output channel
    outputChannel = vscode.window.createOutputChannel('tRust Verification');
    context.subscriptions.push(outputChannel);

    // Create status bar item
    statusBarItem = vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Left, 100);
    statusBarItem.command = 'trust.verify';
    statusBarItem.tooltip = 'Click to verify current file';
    context.subscriptions.push(statusBarItem);

    // Create decoration types
    verifiedDecoration = vscode.window.createTextEditorDecorationType({
        gutterIconPath: context.asAbsolutePath('icons/verified.svg'),
        gutterIconSize: 'contain',
        after: {
            contentIconPath: context.asAbsolutePath('icons/verified.svg'),
            margin: '0 0 0 0.5em'
        },
        overviewRulerColor: 'green',
        overviewRulerLane: vscode.OverviewRulerLane.Left
    });

    disprovenDecoration = vscode.window.createTextEditorDecorationType({
        gutterIconPath: context.asAbsolutePath('icons/disproven.svg'),
        gutterIconSize: 'contain',
        after: {
            contentIconPath: context.asAbsolutePath('icons/disproven.svg'),
            margin: '0 0 0 0.5em'
        },
        overviewRulerColor: 'red',
        overviewRulerLane: vscode.OverviewRulerLane.Left
    });

    unknownDecoration = vscode.window.createTextEditorDecorationType({
        gutterIconPath: context.asAbsolutePath('icons/unknown.svg'),
        gutterIconSize: 'contain',
        after: {
            contentIconPath: context.asAbsolutePath('icons/unknown.svg'),
            margin: '0 0 0 0.5em'
        },
        overviewRulerColor: 'yellow',
        overviewRulerLane: vscode.OverviewRulerLane.Left
    });

    // Register commands
    context.subscriptions.push(
        vscode.commands.registerCommand('trust.verify', verifyCommand)
    );

    context.subscriptions.push(
        vscode.commands.registerCommand('trust.copySuggestion', async (suggestion: string) => {
            await vscode.env.clipboard.writeText(suggestion);
            vscode.window.setStatusBarMessage('tRust: Suggestion copied', 1500);
        })
    );

    context.subscriptions.push(
        vscode.commands.registerCommand('trust.explainError', async (errorCode: string) => {
            const trustcPath = findTrustc();
            if (!trustcPath) {
                vscode.window.showErrorMessage('trustc not found. Please set trust.trustcPath in settings.');
                return;
            }

            outputChannel.show();
            outputChannel.appendLine(`\n=== tRust Error Explanation: ${errorCode} ===\n`);

            let stdout = '';
            const proc = spawn(trustcPath, ['--explain', errorCode], {
                cwd: vscode.workspace.workspaceFolders?.[0]?.uri.fsPath
            });

            proc.stdout.on('data', (data: Buffer) => {
                stdout += data.toString();
            });

            proc.stderr.on('data', (data: Buffer) => {
                outputChannel.append(data.toString());
            });

            proc.on('close', (code) => {
                if (code === 0 && stdout.trim()) {
                    outputChannel.appendLine(stdout);
                } else {
                    outputChannel.appendLine(`No explanation available for ${errorCode}`);
                }
                outputChannel.appendLine('');
            });

            proc.on('error', (err) => {
                outputChannel.appendLine(`Failed to run trustc --explain: ${err.message}`);
            });
        })
    );

    context.subscriptions.push(
        vscode.commands.registerCommand('trust.verifyWorkspace', verifyWorkspaceCommand)
    );

    context.subscriptions.push(
        vscode.commands.registerCommand('trust.clearCache', async () => {
            const trustcPath = findTrustc();
            if (trustcPath) {
                const proc = spawn(trustcPath, ['--cache-clear']);
                proc.on('close', () => {
                    vscode.window.showInformationMessage('tRust: Verification cache cleared');
                });
            }
        })
    );

    context.subscriptions.push(
        vscode.commands.registerCommand('trust.showCacheStats', async () => {
            const trustcPath = findTrustc();
            if (trustcPath) {
                let output = '';
                const proc = spawn(trustcPath, ['--cache-stats']);
                proc.stdout.on('data', (data: Buffer) => {
                    output += data.toString();
                });
                proc.on('close', () => {
                    outputChannel.show();
                    outputChannel.appendLine('=== Cache Statistics ===');
                    outputChannel.appendLine(output);
                });
            }
        })
    );

    context.subscriptions.push(
        vscode.languages.registerCodeActionsProvider('rust', new TrustCodeActionProvider(), {
            providedCodeActionKinds: TrustCodeActionProvider.providedCodeActionKinds
        })
    );

    // Register CodeLens provider
    codeLensProvider = new TrustCodeLensProvider();
    context.subscriptions.push(
        vscode.languages.registerCodeLensProvider('rust', codeLensProvider)
    );

    // Register showFunctionDetails command for CodeLens clicks
    context.subscriptions.push(
        vscode.commands.registerCommand('trust.showFunctionDetails', (func: TrustFunctionResult) => {
            outputChannel.show();
            outputChannel.appendLine(`\n=== Function Details: ${func.name} ===`);
            outputChannel.appendLine(`Status: ${func.status}`);
            outputChannel.appendLine(`Specs: ${func.specs_count}`);
            if (func.message) {
                outputChannel.appendLine(`Message: ${func.message}`);
            }
            if (func.counterexample) {
                outputChannel.appendLine(`\nCounterexample: ${func.counterexample.description}`);
                if (func.counterexample.inputs.length > 0) {
                    outputChannel.appendLine('Inputs:');
                    for (const input of func.counterexample.inputs) {
                        outputChannel.appendLine(`  ${input.name} = ${input.value}`);
                    }
                }
            }
            if (func.spec_hash) {
                outputChannel.appendLine(`\nspec_hash: ${func.spec_hash}`);
            }
            if (func.function_hash) {
                outputChannel.appendLine(`function_hash: ${func.function_hash}`);
            }
            outputChannel.appendLine('');
        })
    );

    // Register event handlers
    const config = vscode.workspace.getConfiguration('trust');

    if (config.get<boolean>('verifyOnSave', true)) {
        context.subscriptions.push(
            vscode.workspace.onDidSaveTextDocument(async (document) => {
                if (document.languageId === 'rust') {
                    const editor = vscode.window.activeTextEditor;
                    if (editor && editor.document === document) {
                        await verifyCommand();
                    }
                }
            })
        );
    }

    if (config.get<boolean>('verifyOnOpen', false)) {
        context.subscriptions.push(
            vscode.window.onDidChangeActiveTextEditor(async (editor) => {
                if (editor && editor.document.languageId === 'rust') {
                    await verifyCommand();
                }
            })
        );
    }

    outputChannel.appendLine('tRust Verification extension activated');
}

/**
 * Extension deactivation
 */
export function deactivate(): void {
    diagnosticCollection?.clear();
    diagnosticCollection?.dispose();
}
