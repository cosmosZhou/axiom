import { getContextBefore, highlightLine, processLine } from "../line/highlight.js"
import { copyState } from "../modes.js"
import { bind, indexOf } from "../util/misc.js"
import { regLineChange, adjustView, countDirtyView, resetView } from "./view_tracking.js"

// HIGHLIGHT WORKER
import { sawCollapsedSpans } from "../line/saw_special_spans.js"
import { heightAtLine, visualLineEndNo, visualLineNo, findMaxLine } from "../line/spans.js"
import { getLine, lineNumberFor } from "../line/utils_line.js"
import { getDimensions, displayWidth, measureChar, scrollGap, cursorCoords, paddingTop, displayHeight, paddingVert, textHeight, estimateCoords} from "../measurement/position_measurement.js"

import { mac, webkit, phantom, gecko } from "../util/browser.js"
import { activeElt, removeChildren, contains, elt, addClass, rmClass  } from "../util/dom.js"
import { buildLineElement, updateLineForChanges } from "./update_line.js"
import { maybeUpdateLineNumberWidth, setScrollLeft } from "./line_numbers.js"
import { updateHeightsInViewport, visibleLines } from "./update_lines.js"
import { updateSelection, restartBlink } from "./selection.js"
// operations.js
import { startOperation } from "./operations.js"
import { clipPos, Pos } from "../line/pos.js"
import { signal, signalDOMEvent } from "../util/event.js"
import { finishOperation } from "../util/operation_group.js"

import { ensureFocus } from "./focus.js"
import { measureForScrollbars, updateScrollbars, scrollbarModel } from "./scrollbars.js"
import { DisplayUpdate, maybeClipScrollbars, setDocumentHeight, updateDisplaySimple } from "./update_display.js"

export function startWorker(cm, time) {
  if (cm.doc.highlightFrontier < cm.display.viewTo)
    cm.state.highlight.set(time, bind(highlightWorker, cm))
}

function highlightWorker(cm) {
  let doc = cm.doc
  if (doc.highlightFrontier >= cm.display.viewTo) return
  let end = +new Date + cm.options.workTime
  let context = getContextBefore(cm, doc.highlightFrontier)
  let changedLines = []

  doc.iter(context.line, Math.min(doc.first + doc.size, cm.display.viewTo + 500), line => {
    if (context.line >= cm.display.viewFrom) { // Visible
      let oldStyles = line.styles
      let resetState = line.text.length > cm.options.maxHighlightLength ? copyState(doc.mode, context.state) : null
      let highlighted = highlightLine(cm, line, context, true)
      if (resetState) context.state = resetState
      line.styles = highlighted.styles
      let oldCls = line.styleClasses, newCls = highlighted.classes
      if (newCls) line.styleClasses = newCls
      else if (oldCls) line.styleClasses = null
      let ischange = !oldStyles || oldStyles.length != line.styles.length ||
        oldCls != newCls && (!oldCls || !newCls || oldCls.bgClass != newCls.bgClass || oldCls.textClass != newCls.textClass)
      for (let i = 0; !ischange && i < oldStyles.length; ++i) ischange = oldStyles[i] != line.styles[i]
      if (ischange) changedLines.push(context.line)
      line.stateAfter = context.save()
      context.nextLine()
    } else {
      if (line.text.length <= cm.options.maxHighlightLength)
        processLine(cm, line.text, context)
      line.stateAfter = context.line % 5 == 0 ? context.save() : null
      context.nextLine()
    }
    if (+new Date > end) {
      startWorker(cm, cm.options.workDelay)
      return true
    }
  })
  doc.highlightFrontier = context.line
  doc.modeFrontier = Math.max(doc.modeFrontier, context.line)
  if (changedLines.length) runInOp(cm, () => {
    for (let i = 0; i < changedLines.length; i++)
      regLineChange(cm, changedLines[i], "text")
  })
}

//update_display.js
function selectionSnapshot(cm) {
  if (cm.hasFocus()) return null
  let active = activeElt()
  if (!active || !contains(cm.display.lineDiv, active)) return null
  let result = {activeElt: active}
  if (window.getSelection) {
    let sel = window.getSelection()
    if (sel.anchorNode && sel.extend && contains(cm.display.lineDiv, sel.anchorNode)) {
      result.anchorNode = sel.anchorNode
      result.anchorOffset = sel.anchorOffset
      result.focusNode = sel.focusNode
      result.focusOffset = sel.focusOffset
    }
  }
  return result
}

function restoreSelection(snapshot) {
  if (!snapshot || !snapshot.activeElt || snapshot.activeElt == activeElt()) return
  snapshot.activeElt.focus()
  if (!/^(INPUT|TEXTAREA)$/.test(snapshot.activeElt.nodeName) &&
      snapshot.anchorNode && contains(document.body, snapshot.anchorNode) && contains(document.body, snapshot.focusNode)) {
    let sel = window.getSelection(), range = document.createRange()
    range.setEnd(snapshot.anchorNode, snapshot.anchorOffset)
    range.collapse(false)
    sel.removeAllRanges()
    sel.addRange(range)
    sel.extend(snapshot.focusNode, snapshot.focusOffset)
  }
}

// Does the actual updating of the line display. Bails out
// (returning false) when there is nothing to be done and forced is
// false.
export function updateDisplayIfNeeded(cm, update) {
  let display = cm.display, doc = cm.doc

  if (update.editorIsHidden) {
    resetView(cm)
    return false
  }

  // Bail out if the visible area is already rendered and nothing changed.
  if (!update.force &&
      update.visible.from >= display.viewFrom && update.visible.to <= display.viewTo &&
      (display.updateLineNumbers == null || display.updateLineNumbers >= display.viewTo) &&
      display.renderedView == display.view && countDirtyView(cm) == 0)
    return false

  if (maybeUpdateLineNumberWidth(cm)) {
    resetView(cm)
    update.dims = getDimensions(cm)
  }

  // Compute a suitable new viewport (from & to)
  let end = doc.first + doc.size
  let from = Math.max(update.visible.from - cm.options.viewportMargin, doc.first)
  let to = Math.min(end, update.visible.to + cm.options.viewportMargin)
  if (display.viewFrom < from && from - display.viewFrom < 20) from = Math.max(doc.first, display.viewFrom)
  if (display.viewTo > to && display.viewTo - to < 20) to = Math.min(end, display.viewTo)
  if (sawCollapsedSpans) {
    from = visualLineNo(cm.doc, from)
    to = visualLineEndNo(cm.doc, to)
  }

  let different = from != display.viewFrom || to != display.viewTo ||
    display.lastWrapHeight != update.wrapperHeight || display.lastWrapWidth != update.wrapperWidth
  adjustView(cm, from, to)

  display.viewOffset = heightAtLine(getLine(cm.doc, display.viewFrom))
  // Position the mover div to align with the current scroll position
  cm.display.mover.style.top = display.viewOffset + "px"

  let toUpdate = countDirtyView(cm)
  if (!different && toUpdate == 0 && !update.force && display.renderedView == display.view &&
      (display.updateLineNumbers == null || display.updateLineNumbers >= display.viewTo))
    return false

  // For big changes, we hide the enclosing element during the
  // update, since that speeds up the operations on most browsers.
  let selSnapshot = selectionSnapshot(cm)
  if (toUpdate > 4) display.lineDiv.style.display = "none"
  patchDisplay(cm, display.updateLineNumbers, update.dims)
  if (toUpdate > 4) display.lineDiv.style.display = ""
  display.renderedView = display.view
  // There might have been a widget with a focused element that got
  // hidden or updated, if so re-focus it.
  restoreSelection(selSnapshot)

  // Prevent selection and cursors from interfering with the scroll
  // width and height.
  removeChildren(display.cursorDiv)
  removeChildren(display.selectionDiv)
  display.gutters.style.height = display.sizer.style.minHeight = 0

  if (different) {
    display.lastWrapHeight = update.wrapperHeight
    display.lastWrapWidth = update.wrapperWidth
    startWorker(cm, 400)
  }

  display.updateLineNumbers = null

  return true
}

// Sync the actual display DOM structure with display.view, removing
// nodes for lines that are no longer in view, and creating the ones
// that are not there yet, and updating the ones that are out of
// date.
function patchDisplay(cm, updateNumbersFrom, dims) {
  let display = cm.display, lineNumbers = cm.options.lineNumbers
  let container = display.lineDiv, cur = container.firstChild

  function rm(node) {
    let next = node.nextSibling
    // Works around a throw-scroll bug in OS X Webkit
    if (webkit && mac && cm.display.currentWheelTarget == node)
      node.style.display = "none"
    else
      node.parentNode.removeChild(node)
    return next
  }

  let view = display.view, lineN = display.viewFrom
  // Loop over the elements in the view, syncing cur (the DOM nodes
  // in display.lineDiv) with the view as we go.
  for (let i = 0; i < view.length; i++) {
    let lineView = view[i]
    if (lineView.hidden) {
    } else if (!lineView.node || lineView.node.parentNode != container) { // Not drawn yet
      let node = buildLineElement(cm, lineView, lineN, dims)
      container.insertBefore(node, cur)
    } else { // Already drawn
      while (cur != lineView.node) cur = rm(cur)
      let updateNumber = lineNumbers && updateNumbersFrom != null &&
        updateNumbersFrom <= lineN && lineView.lineNumber
      if (lineView.changes) {
        if (indexOf(lineView.changes, "gutter") > -1) updateNumber = false
        updateLineForChanges(cm, lineView, lineN, dims)
      }
      if (updateNumber) {
        removeChildren(lineView.lineNumber)
        lineView.lineNumber.appendChild(document.createTextNode(lineNumberFor(cm.options, lineN)))
      }
      cur = lineView.node.nextSibling
    }
    lineN += lineView.size
  }
  while (cur) cur = rm(cur)
}

export function postUpdateDisplay(cm, update) {
  let viewport = update.viewport

  for (let first = true;; first = false) {
    if (!first || !cm.options.lineWrapping || update.oldDisplayWidth == displayWidth(cm)) {
      // Clip forced viewport to actual scrollable area.
      if (viewport && viewport.top != null)
        viewport = {top: Math.min(cm.doc.height + paddingVert(cm.display) - displayHeight(cm), viewport.top)}
      // Updated line heights might result in the drawn area not
      // actually covering the viewport. Keep looping until it does.
      update.visible = visibleLines(cm.display, cm.doc, viewport)
      if (update.visible.from >= cm.display.viewFrom && update.visible.to <= cm.display.viewTo)
        break
    } else if (first) {
      update.visible = visibleLines(cm.display, cm.doc, viewport)
    }
    if (!updateDisplayIfNeeded(cm, update)) break
    updateHeightsInViewport(cm)
    let barMeasure = measureForScrollbars(cm)
    updateSelection(cm)
    updateScrollbars(cm, barMeasure)
    setDocumentHeight(cm, barMeasure)
    update.force = false
  }

  update.signal(cm, "update", cm)
  if (cm.display.viewFrom != cm.display.reportedViewFrom || cm.display.viewTo != cm.display.reportedViewTo) {
    update.signal(cm, "viewportChange", cm, cm.display.viewFrom, cm.display.viewTo)
    cm.display.reportedViewFrom = cm.display.viewFrom; cm.display.reportedViewTo = cm.display.viewTo
  }
}

//operations.js:

// Finish an operation, updating the display and signalling delayed events
export function endOperation(cm) {
  let op = cm.curOp
  if (op) finishOperation(op, group => {
    for (let i = 0; i < group.ops.length; i++)
      group.ops[i].cm.curOp = null
    endOperations(group)
  })
}

// The DOM updates done when an operation finishes are batched so
// that the minimum number of relayouts are required.
function endOperations(group) {
  let ops = group.ops
  for (let i = 0; i < ops.length; i++) // Read DOM
    endOperation_R1(ops[i])
  for (let i = 0; i < ops.length; i++) // Write DOM (maybe)
    endOperation_W1(ops[i])
  for (let i = 0; i < ops.length; i++) // Read DOM
    endOperation_R2(ops[i])
  for (let i = 0; i < ops.length; i++) // Write DOM (maybe)
    endOperation_W2(ops[i])
  for (let i = 0; i < ops.length; i++) // Read DOM
    endOperation_finish(ops[i])
}

function endOperation_R1(op) {
  let cm = op.cm, display = cm.display
  maybeClipScrollbars(cm)
  if (op.updateMaxLine) findMaxLine(cm)

  op.mustUpdate = op.viewChanged || op.forceUpdate || op.scrollTop != null ||
    op.scrollToPos && (op.scrollToPos.from.line < display.viewFrom ||
                       op.scrollToPos.to.line >= display.viewTo) ||
    display.maxLineChanged && cm.options.lineWrapping
  op.update = op.mustUpdate &&
    new DisplayUpdate(cm, op.mustUpdate && {top: op.scrollTop, ensure: op.scrollToPos}, op.forceUpdate)
}

function endOperation_W1(op) {
  op.updatedDisplay = op.mustUpdate && updateDisplayIfNeeded(op.cm, op.update)
}

function endOperation_R2(op) {
  let cm = op.cm, display = cm.display
  if (op.updatedDisplay) updateHeightsInViewport(cm)

  op.barMeasure = measureForScrollbars(cm)

  // If the max line changed since it was last measured, measure it,
  // and ensure the document's width matches it.
  // updateDisplay_W2 will use these properties to do the actual resizing
  if (display.maxLineChanged && !cm.options.lineWrapping) {
    op.adjustWidthTo = measureChar(cm, display.maxLine, display.maxLine.text.length).left + 3
    cm.display.sizerWidth = op.adjustWidthTo
    op.barMeasure.scrollWidth =
      Math.max(display.scroller.clientWidth, display.sizer.offsetLeft + op.adjustWidthTo + scrollGap(cm) + cm.display.barWidth)
    op.maxScrollLeft = Math.max(0, display.sizer.offsetLeft + op.adjustWidthTo - displayWidth(cm))
  }

  if (op.updatedDisplay || op.selectionChanged)
    op.preparedSelection = display.input.prepareSelection()
}

function endOperation_W2(op) {
  let cm = op.cm

  if (op.adjustWidthTo != null) {
    cm.display.sizer.style.minWidth = op.adjustWidthTo + "px"
    if (op.maxScrollLeft < cm.doc.scrollLeft)
      setScrollLeft(cm, Math.min(cm.display.scroller.scrollLeft, op.maxScrollLeft), true)
    cm.display.maxLineChanged = false
  }

  let takeFocus = op.focus && op.focus == activeElt()
  if (op.preparedSelection)
    cm.display.input.showSelection(op.preparedSelection, takeFocus)
  if (op.updatedDisplay || op.startHeight != cm.doc.height)
    updateScrollbars(cm, op.barMeasure)
  if (op.updatedDisplay)
    setDocumentHeight(cm, op.barMeasure)

  if (op.selectionChanged) restartBlink(cm)

  if (cm.state.focused && op.updateInput)
    cm.display.input.reset(op.typing)
  if (takeFocus) ensureFocus(op.cm)
}

function endOperation_finish(op) {
  let cm = op.cm, display = cm.display, doc = cm.doc

  if (op.updatedDisplay) postUpdateDisplay(cm, op.update)

  // Abort mouse wheel delta measurement, when scrolling explicitly
  if (display.wheelStartX != null && (op.scrollTop != null || op.scrollLeft != null || op.scrollToPos))
    display.wheelStartX = display.wheelStartY = null

  // Propagate the scroll position to the actual DOM scroller
  if (op.scrollTop != null) setScrollTop(cm, op.scrollTop, op.forceScroll)

  if (op.scrollLeft != null) setScrollLeft(cm, op.scrollLeft, true, true)
  // If we need to scroll a specific position into view, do so.
  if (op.scrollToPos) {
    let rect = scrollPosIntoView(cm, clipPos(doc, op.scrollToPos.from),
                                 clipPos(doc, op.scrollToPos.to), op.scrollToPos.margin)
    maybeScrollWindow(cm, rect)
  }

  // Fire events for markers that are hidden/unidden by editing or
  // undoing
  let hidden = op.maybeHiddenMarkers, unhidden = op.maybeUnhiddenMarkers
  if (hidden) for (let i = 0; i < hidden.length; ++i)
    if (!hidden[i].lines.length) signal(hidden[i], "hide")
  if (unhidden) for (let i = 0; i < unhidden.length; ++i)
    if (unhidden[i].lines.length) signal(unhidden[i], "unhide")

  if (display.wrapper.offsetHeight)
    doc.scrollTop = cm.display.scroller.scrollTop

  // Fire change events, and delayed event handlers
  if (op.changeObjs)
    signal(cm, "changes", cm, op.changeObjs)
  if (op.update)
    op.update.finish()
}

// Run the given function in an operation
export function runInOp(cm, f) {
  if (cm.curOp) return f()
  startOperation(cm)
  try { return f() }
  finally { endOperation(cm) }
}
// Wraps a function in an operation. Returns the wrapped function.
export function operation(cm, f) {
  return function() {
    if (cm.curOp) return f.apply(cm, arguments)
    startOperation(cm)
    try { return f.apply(cm, arguments) }
    finally { endOperation(cm) }
  }
}
// Used to add methods to editor and doc instances, wrapping them in
// operations.
export function methodOp(f) {
  return function() {
    if (this.curOp) return f.apply(this, arguments)
    startOperation(this)
    try { return f.apply(this, arguments) }
    finally { endOperation(this) }
  }
}
export function docMethodOp(f) {
  return function() {
    let cm = this.cm
    if (!cm || cm.curOp) return f.apply(this, arguments)
    startOperation(cm)
    try { return f.apply(this, arguments) }
    finally { endOperation(cm) }
  }
}

// If an editor sits on the top or bottom of the window, partially
// scrolled out of view, this ensures that the cursor is visible.
export function maybeScrollWindow(cm, rect) {
  if (signalDOMEvent(cm, "scrollCursorIntoView")) return

  let display = cm.display, box = display.sizer.getBoundingClientRect(), doScroll = null
  if (rect.top + box.top < 0) doScroll = true
  else if (rect.bottom + box.top > (window.innerHeight || document.documentElement.clientHeight)) doScroll = false
  if (doScroll != null && !phantom) {
    let scrollNode = elt("div", "\u200b", null, `position: absolute;
                         top: ${rect.top - display.viewOffset - paddingTop(cm.display)}px;
                         height: ${rect.bottom - rect.top + scrollGap(cm) + display.barHeight}px;
                         left: ${rect.left}px; width: ${Math.max(2, rect.right - rect.left)}px;`)
    cm.display.lineSpace.appendChild(scrollNode)
    scrollNode.scrollIntoView(doScroll)
    cm.display.lineSpace.removeChild(scrollNode)
  }
}

// Scroll a given position into view (immediately), verifying that
// it actually became visible (as line heights are accurately
// measured, the position of something may 'drift' during drawing).
export function scrollPosIntoView(cm, pos, end, margin) {
  if (margin == null) margin = 0
  let rect
  if (!cm.options.lineWrapping && pos == end) {
    // Set pos and end to the cursor positions around the character pos sticks to
    // If pos.sticky == "before", that is around pos.ch - 1, otherwise around pos.ch
    // If pos == Pos(_, 0, "before"), pos and end are unchanged
    end = pos.sticky == "before" ? Pos(pos.line, pos.ch + 1, "before") : pos
    pos = pos.ch ? Pos(pos.line, pos.sticky == "before" ? pos.ch - 1 : pos.ch, "after") : pos
  }
  for (let limit = 0; limit < 5; limit++) {
    let changed = false
    let coords = cursorCoords(cm, pos)
    let endCoords = !end || end == pos ? coords : cursorCoords(cm, end)
    rect = {left: Math.min(coords.left, endCoords.left),
            top: Math.min(coords.top, endCoords.top) - margin,
            right: Math.max(coords.left, endCoords.left),
            bottom: Math.max(coords.bottom, endCoords.bottom) + margin}
    let scrollPos = calculateScrollPos(cm, rect)
    let startTop = cm.doc.scrollTop, startLeft = cm.doc.scrollLeft
    if (scrollPos.scrollTop != null) {
      updateScrollTop(cm, scrollPos.scrollTop)
      if (Math.abs(cm.doc.scrollTop - startTop) > 1) changed = true
    }
    if (scrollPos.scrollLeft != null) {
      setScrollLeft(cm, scrollPos.scrollLeft)
      if (Math.abs(cm.doc.scrollLeft - startLeft) > 1) changed = true
    }
    if (!changed) break
  }
  return rect
}

// Scroll a given set of coordinates into view (immediately).
export function scrollIntoView(cm, rect) {
  let scrollPos = calculateScrollPos(cm, rect)
  if (scrollPos.scrollTop != null) updateScrollTop(cm, scrollPos.scrollTop)
  if (scrollPos.scrollLeft != null) setScrollLeft(cm, scrollPos.scrollLeft)
}

export function setScrollTop(cm, val, forceScroll) {
  val = Math.max(0, Math.min(cm.display.scroller.scrollHeight - cm.display.scroller.clientHeight, val))
  if (cm.display.scroller.scrollTop == val && !forceScroll) return
  cm.doc.scrollTop = val
  cm.display.scrollbars.setScrollTop(val)
  if (cm.display.scroller.scrollTop != val) cm.display.scroller.scrollTop = val
}

// Calculate a new scroll position needed to scroll the given
// rectangle into view. Returns an object with scrollTop and
// scrollLeft properties. When these are undefined, the
// vertical/horizontal position does not need to be adjusted.
function calculateScrollPos(cm, rect) {
  let display = cm.display, snapMargin = textHeight(cm.display)
  if (rect.top < 0) rect.top = 0
  let screentop = cm.curOp && cm.curOp.scrollTop != null ? cm.curOp.scrollTop : display.scroller.scrollTop
  let screen = displayHeight(cm), result = {}
  if (rect.bottom - rect.top > screen) rect.bottom = rect.top + screen
  let docBottom = cm.doc.height + paddingVert(display)
  let atTop = rect.top < snapMargin, atBottom = rect.bottom > docBottom - snapMargin
  if (rect.top < screentop) {
    result.scrollTop = atTop ? 0 : rect.top
  } else if (rect.bottom > screentop + screen) {
    let newTop = Math.min(rect.top, (atBottom ? docBottom : rect.bottom) - screen)
    if (newTop != screentop) result.scrollTop = newTop
  }

  let gutterSpace = cm.options.fixedGutter ? 0 : display.gutters.offsetWidth
  let screenleft = cm.curOp && cm.curOp.scrollLeft != null ? cm.curOp.scrollLeft : display.scroller.scrollLeft - gutterSpace
  let screenw = displayWidth(cm) - display.gutters.offsetWidth
  let tooWide = rect.right - rect.left > screenw
  if (tooWide) rect.right = rect.left + screenw
  if (rect.left < 10)
    result.scrollLeft = 0
  else if (rect.left < screenleft)
    result.scrollLeft = Math.max(0, rect.left + gutterSpace - (tooWide ? 0 : 10))
  else if (rect.right > screenw + screenleft - 3)
    result.scrollLeft = rect.right + (tooWide ? 0 : 10) - screenw
  return result
}

export function scrollToCoordsRange(cm, from, to, margin) {
  let sPos = calculateScrollPos(cm, {
    left: Math.min(from.left, to.left),
    top: Math.min(from.top, to.top) - margin,
    right: Math.max(from.right, to.right),
    bottom: Math.max(from.bottom, to.bottom) + margin
  })
  scrollToCoords(cm, sPos.scrollLeft, sPos.scrollTop)
}

// Sync the scrollable area and scrollbars, ensure the viewport
// covers the visible area.
export function updateScrollTop(cm, val) {
  if (Math.abs(cm.doc.scrollTop - val) < 2) return
  if (!gecko) updateDisplaySimple(cm, {top: val})
  setScrollTop(cm, val, true)
  if (gecko) updateDisplaySimple(cm)
  startWorker(cm, 100)
}

export function initScrollbars(cm) {
  if (cm.display.scrollbars) {
    cm.display.scrollbars.clear()
    if (cm.display.scrollbars.addClass)
      rmClass(cm.display.wrapper, cm.display.scrollbars.addClass)
  }

  cm.display.scrollbars = new scrollbarModel[cm.options.scrollbarStyle](node => {
    cm.display.wrapper.insertBefore(node, cm.display.scrollbarFiller)
    // Prevent clicks in the scrollbars from killing focus
    on(node, "mousedown", () => {
      if (cm.state.focused) setTimeout(() => cm.display.input.focus(), 0)
    })
    node.setAttribute("cm-not-content", "true")
  }, (pos, axis) => {
    if (axis == "horizontal") setScrollLeft(cm, pos)
    else updateScrollTop(cm, pos)
  }, cm)
  if (cm.display.scrollbars.addClass)
    addClass(cm.display.wrapper, cm.display.scrollbars.addClass)
}

export function scrollToCoords(cm, x, y) {
  if (x != null || y != null) resolveScrollToPos(cm)
  if (x != null) cm.curOp.scrollLeft = x
  if (y != null) cm.curOp.scrollTop = y
}

// SCROLLING THINGS INTO VIEW

// Store a relative adjustment to the scroll position in the current
// operation (to be applied when the operation finishes).
export function addToScrollTop(cm, top) {
  if (top == null) return
  resolveScrollToPos(cm)
  cm.curOp.scrollTop = (cm.curOp.scrollTop == null ? cm.doc.scrollTop : cm.curOp.scrollTop) + top
}

// Make sure that at the end of the operation the current cursor is
// shown.
export function ensureCursorVisible(cm) {
  resolveScrollToPos(cm)
  let cur = cm.getCursor()
  cm.curOp.scrollToPos = {from: cur, to: cur, margin: cm.options.cursorScrollMargin}
}

export function scrollToRange(cm, range) {
  resolveScrollToPos(cm)
  cm.curOp.scrollToPos = range
}

// When an operation has its scrollToPos property set, and another
// scroll action is applied before the end of the operation, this
// 'simulates' scrolling that position into view in a cheap way, so
// that the effect of intermediate scroll commands is not ignored.
function resolveScrollToPos(cm) {
  let range = cm.curOp.scrollToPos
  if (range) {
    cm.curOp.scrollToPos = null
    let from = estimateCoords(cm, range.from), to = estimateCoords(cm, range.to)
    scrollToCoordsRange(cm, from, to, range.margin)
  }
}

