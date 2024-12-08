<?php
function test() {
    $physicalText = "firstly,&nbsp;<div><b>this&nbsp;is&nbsp;<I>an&nbsp;<font color='red'><i>italic</i>&nbsp;<u>&lt;underline&gt;</u><mspace /></font>, simply put</b>,&nbsp;this&nbsp;is&nbsp;an&nbsp;italic&nbsp;text,&nbsp;</I>with&nbsp;something&emsp;<u>&lt;underlined&gt;</u>;</div>&ensp;<b>another&nbsp;bold&nbsp;text&nbsp;is&nbsp;followed.&nbsp;</b>At&nbsp;last,&nbsp;there&nbsp;a&nbsp;plain&nbsp;text.";
//     $physicalText = "<div><b><I></b></I>with&nbsp;";
        
    $richText = construct_rich_text($physicalText);
    error_log($richText);
    error_log("physical text = ".$richText->physicalText);
    error_log(" logical text = ".$richText->text);
    error_log(" style_traits = ".std\encode($richText->style_traits));
    
    
    $start= 20;
    $stop = 39;
    error_log("the logical text is :");
    error_log(std\slice($richText->text, $start, $stop));
    error_log("its style trait is :");
    error_log(std\encode(std\slice($richText->style_traits, $start, $stop)));
    
    [$start, $stop] = $richText->getPhysicalIndices($start, $stop);
    error_log("its original physical text is:");
    error_log(std\slice($physicalText, $start, $stop));
}

require './RichText.php';

test();
?>