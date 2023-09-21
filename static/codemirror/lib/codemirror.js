//subs ^((?!^export (let|function|class|defualt) (\w+).*).)*[\r\n]+
//with 
//subs export (let|function|class|defualt) (\w+) *=.*[\r\n]+
//with \1,
import {gecko, ie, ie_version, webkit, chrome, presto, safari, mac_geMountainLion, phantom, ios, android, mobile, mac, chromeOS, windows, flipCtrlCmd, captureRightClick} from '../src/util/browser.js'

import {classTest, rmClass, removeChildren, removeChildrenAndAdd, elt, eltP, range, contains, activeElt, addClass, joinClasses, selectInput} from '../src/util/dom.js'

import {bind, copyObj, countColumn, Delayed, indexOf, scrollerGap, Pass, sel_dontScroll, findColumn, spaceStr, lst, map, insertSorted, createObj, isWordCharBasic, isWordChar, isEmpty, isExtendingChar, skipExtendingChars, findFirst} from '../src/util/misc.js' 

import {iterateBidiSections, bidiOther, getBidiPartAt, getOrder} from '../src/util/bidi.js'

import {on, getHandlers, off, signal, signalDOMEvent, signalCursorActivity, hasHandler, eventMixin, e_preventDefault, e_stopPropagation, e_defaultPrevented, e_stop, e_target, e_button} from '../src/util/event.js'

import {dragAndDrop, zeroWidthElement, hasBadBidiRects, splitLinesAuto, hasSelection, hasCopyEvent, hasBadZoomedRects} from '../src/util/feature_detection.js'

import {modes, defineMode, defineMIME, resolveMode, getMode, modeExtensions, extendMode, copyState, innerMode, startState} from '../src/modes.js'

import StringStream from '../src/util/StringStream.js'

import {getLine, getBetween, getLines, updateLineHeight, lineNo, lineAtHeight, isLine, lineNumberFor} from '../src/line/utils_line.js'

import {cmp, equalCursorPos, copyPos, maxPos, minPos, clipLine, clipPos, clipPosArray} from '../src/line/pos.js'

import {highlightLine, getLineStyles, getContextBefore, processLine, takeToken, retreatFrontier} from '../src/line/highlight.js'

import {sawReadOnlySpans, seeReadOnlySpans, seeCollapsedSpans} from '../src/line/saw_special_spans.js'

import {MarkedSpan, getMarkedSpanFor, removeMarkedSpan, addMarkedSpan, stretchSpansOverChange, removeReadOnlyRanges, detachMarkedSpans, attachMarkedSpans, compareCollapsedMarkers, collapsedSpanAtStart, collapsedSpanAtEnd, collapsedSpanAround, conflictingCollapsedRange, visualLine, visualLineEnd, visualLineContinued, visualLineNo, visualLineEndNo, lineIsHidden, heightAtLine, lineLength, findMaxLine} from '../src/line/spans.js'

import {Line, updateLine, cleanUpLine, buildLineContent, defaultSpecialCharPlaceholder, LineView, buildViewArray} from '../src/line/line_data.js'

import {pushOperation, finishOperation, signalLater, updateGutterSpace} from '../src/util/operation_group.js'

import {updateLineForChanges, buildLineElement} from '../src/display/update_line.js'

import {widgetHeight, eventInWidget} from '../src/measurement/widgets.js'

import {paddingTop, paddingVert, paddingH, scrollGap, displayWidth, displayHeight, mapFromLineView, measureChar, findViewForLine, prepareMeasureForLine, measureCharPrepared, nodeAndOffsetInLineMap, clearLineMeasurementCacheFor, clearLineMeasurementCache, clearCaches, intoCoordSystem, fromCoordSystem, charCoords, cursorCoords, estimateCoords, coordsChar, wrappedLineExtentChar, textHeight, charWidth, getDimensions, compensateForHScroll, estimateHeight, estimateLineHeights, posFromMouse, findViewIndex} from '../src/measurement/position_measurement.js'

import {regChange, regLineChange, resetView, adjustView, countDirtyView} from '../src/display/view_tracking.js'

import {updateSelection, prepareSelection, drawSelectionCursor, restartBlink} from '../src/display/selection.js'

import {ensureFocus, delayBlurEvent, onFocus} from '../src/display/focus.js'

import {onBlur} from '../src/display/blur.js'

import {updateHeightsInViewport, visibleLines} from '../src/display/update_lines.js'

import {measureForScrollbars, updateScrollbars, scrollbarModel} from '../src/display/scrollbars.js'

import {startOperation} from '../src/display/operations.js'

import {startWorker, updateDisplayIfNeeded, endOperation, runInOp, operation, methodOp, docMethodOp, postUpdateDisplay, maybeScrollWindow, scrollPosIntoView, scrollIntoView, setScrollTop, scrollToCoordsRange, updateScrollTop, initScrollbars, scrollToCoords, addToScrollTop, ensureCursorVisible, scrollToRange} from '../src/display/highlight_worker.js'

import {DisplayUpdate, maybeClipScrollbars, updateDisplaySimple, setDocumentHeight} from '../src/display/update_display.js'

import {alignHorizontally, maybeUpdateLineNumberWidth, setScrollLeft} from '../src/display/line_numbers.js'

import {getGutters, renderGutters, updateGutters} from '../src/display/gutters.js'

import {Display} from '../src/display/Display.js'

import {wheelEventPixels, onScrollWheel} from '../src/display/scroll_events.js'

import {Selection, Range, normalizeSelection, simpleSelection} from '../src/model/selection.js'

import {changeEnd, computeSelAfterChange, computeReplacedSel} from '../src/model/change_measurement.js'

import {loadMode, resetModeState} from '../src/display/mode_state.js'

import {isWholeLineUpdate, updateDoc, linkedDocs, attachDoc, directionChanged} from '../src/model/document_data.js'

import {History, historyChangeFromChange, addChangeToHistory, addSelectionToHistory, pushSelectionToHistory, mergeOldSpans, copyHistoryArray} from '../src/model/history.js'

import {extendRange, extendSelection, extendSelections, replaceOneSelection, setSimpleSelection, setSelectionReplaceHistory, setSelection, setSelectionNoUndo, reCheckSelection, skipAtomic, selectAll} from '../src/model/selection_updates.js'

import {makeChange, makeChangeFromHistory, replaceRange, changeLine} from '../src/model/changes.js'

import {LeafChunk, BranchChunk} from '../src/model/chunk.js'

import {LineWidget, addLineWidget} from '../src/model/line_widget.js'

import {TextMarker, markText, SharedTextMarker, findSharedMarkers, copySharedMarkers, detachSharedMarkers} from '../src/model/mark_text.js'

import Doc from '../src/model/Doc.js'

import {onDrop, onDragStart, onDragOver, clearDragCursor} from '../src/edit/drop_events.js'

import {ensureGlobalHandlers} from '../src/edit/global_events.js'

import {keyNames} from '../src/input/keynames.js'

import {keyMap, normalizeKeyMap, lookupKey, isModifierKey, addModifierNames, keyName, getKeyMap} from '../src/input/keymap.js'

import {deleteNearSelection} from '../src/edit/deleteNearSelection.js'

import {moveLogically, endOfLine, moveVisually} from '../src/input/movement.js'

import {commands} from '../src/edit/commands.js'

import {dispatchKey, onKeyDown, onKeyUp, onKeyPress} from '../src/edit/key_events.js'

import {onMouseDown, clickInGutter, onContextMenu} from '../src/edit/mouse_events.js'

import {themeChanged} from '../src/edit/utils.js'

import {Init, defaults, optionHandlers, defineOptions} from '../src/edit/options.js'

import {indentLine} from '../src/input/indent.js'

import {lastCopied, setLastCopied, applyTextInput, handlePaste, triggerElectric, copyableRanges, disableBrowserMagic, hiddenTextarea} from '../src/input/input.js'

import addEditorMethods from '../src/edit/methods.js'

import ContentEditableInput from '../src/input/ContentEditableInput.js'

import {fromTextArea} from '../src/edit/fromTextArea.js'

import {addLegacyProps} from '../src/edit/legacy.js'

import {CodeMirror} from '../src/edit/main.js'

(function(global, factory) {
	typeof exports === 'object' && typeof module !== 'undefined' ? module.exports = factory() :
		typeof define === 'function' && define.amd ? define(factory) :
			(global = global || self, global.CodeMirror = factory());
}(this, (function() {
	'use strict';
	return CodeMirror;
})));
