import { displayWidth, getDimensions, scrollGap } from "../measurement/position_measurement.js"
import { hasHandler, signal } from "../util/event.js"
import { measureForScrollbars, updateScrollbars } from "./scrollbars.js"
import { updateSelection } from "./selection.js"
import { updateHeightsInViewport, visibleLines } from "./update_lines.js"

// DISPLAY DRAWING

export class DisplayUpdate {
  constructor(cm, viewport, force) {
    let display = cm.display

    this.viewport = viewport
    // Store some values that we'll need later (but don't want to force a relayout for)
    this.visible = visibleLines(display, cm.doc, viewport)
    this.editorIsHidden = !display.wrapper.offsetWidth
    this.wrapperHeight = display.wrapper.clientHeight
    this.wrapperWidth = display.wrapper.clientWidth
    this.oldDisplayWidth = displayWidth(cm)
    this.force = force
    this.dims = getDimensions(cm)
    this.events = []
  }

  signal(emitter, type) {
    if (hasHandler(emitter, type))
      this.events.push(arguments)
  }
  finish() {
    for (let i = 0; i < this.events.length; i++)
      signal.apply(null, this.events[i])
  }
}

export function maybeClipScrollbars(cm) {
  let display = cm.display
  if (!display.scrollbarsClipped && display.scroller.offsetWidth) {
    display.nativeBarWidth = display.scroller.offsetWidth - display.scroller.clientWidth
    display.heightForcer.style.height = scrollGap(cm) + "px"
    display.sizer.style.marginBottom = -display.nativeBarWidth + "px"
    display.sizer.style.borderRightWidth = scrollGap(cm) + "px"
    display.scrollbarsClipped = true
  }
}

export function updateDisplaySimple(cm, viewport) {
  let update = new DisplayUpdate(cm, viewport)
  if (updateDisplayIfNeeded(cm, update)) {
    updateHeightsInViewport(cm)
    postUpdateDisplay(cm, update)
    let barMeasure = measureForScrollbars(cm)
    updateSelection(cm)
    updateScrollbars(cm, barMeasure)
    setDocumentHeight(cm, barMeasure)
    update.finish()
  }
}

export function setDocumentHeight(cm, measure) {
  cm.display.sizer.style.minHeight = measure.docHeight + "px"
  cm.display.heightForcer.style.top = measure.docHeight + "px"
  cm.display.gutters.style.height = (measure.docHeight + cm.display.barHeight + scrollGap(cm)) + "px"
}
