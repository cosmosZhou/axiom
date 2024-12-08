import { rmClass } from "../util/dom.js"
import { signal } from "../util/event.js"

export function onBlur(cm, e) {
  if (cm.state.delayingBlurEvent) return

  if (cm.state.focused) {
    signal(cm, "blur", cm, e)
    cm.state.focused = false
    rmClass(cm.display.wrapper, "CodeMirror-focused")
  }
  clearInterval(cm.display.blinker)
  setTimeout(() => { if (!cm.state.focused) cm.display.shift = false }, 150)
}
