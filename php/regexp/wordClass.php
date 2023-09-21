<?php
require_once __DIR__.'/Lexeme.php';
require_once __DIR__.'/balancedMatch.php';

//select distinct regexp_substr(text, "\\b[a-z]+omo\\b") from markush where text regexp "\\b[a-z]+omo\\b";

$wordClass = [
    "number" => "zero|one|two|three|four|five|six|seven|eight|nine|ten|eleven|twelve|thirteen|fourteen|fifteen|sixteen|seventeen|eighteen|nineteen|twenty|thirty|fourty|fifty|sixty|seventy|eighty|ninety|hundrens?|thousands?|millions?",
    "preposition" => "of|from|for|to|into|among|at|by|in|below|as|with(in|out)?|behind|ahead|onto|on|about|under|above|over|after|before|through(out)?|until|inside|outside|since",
    'adv' => '[a-z]+(?<!\b(fami|name|assemb|(under|over)?supp|app|anoma|po|[A-Z])|[^p]o|x|alk)ly|further',
    'adj' => '(non|un)?[a-z]+(able|tive|[tlnrm]ic|[sl]ent|ical|[a-z]ing|rous|bile|ible)|linear|lower|higher|low|straight|(un)?necessary|honorary|imaginary|elementary|stationary|temporary|sedentary|mercenary|(in)?appropriate',

    'arithmetic' => '[=≠<>≤≥≦≧]|>=|<=|!=',
    'logic' => 'or|and|and/or',
    'participle' => '[a-z]+ed|alit|arisen|awoken|beaten|become|been|befallen|begotten|begun|beheld|beholden|bent|bereft|besought|bet|bidden|bit|bitten|blent|blest|blown|born|borne|bought|bound|broadcast|broken|brought|built|burnt|burst|cast|caught|chosen|clad|cleft|cloven|clung|come|cost|could|covert|crept|cut|dealt|done|drawn|dreamt|driven|drunk|dug|dwelt|eaten|fallen|felt|feud|flown|flung|forbidden|forecast|forgiven|forgot|forgotten|forsaken|forsworn|fought|found|frozen|gainsaid|gelt|girt|given|gone|got|gotten|graven|ground|grown|had|heard|held|het|hewn|hid|hidden|hit|hove|hung|hurt|interwoven|kept|knelt|known|laden|laid|lain|leant|leapt|learnt|left|lent|let|lit|lost|made|meant|met|might|mistaken|misunderstood|molten|outgrown|overcome|overseen|paid|proven|put|quit|read|reft|rent|restraint|ridden|risen|riven|run|rung|said|sat|sawn|seen|sent|set|sewn|shaken|shaven|shod|shone|shorn|shot|should|shown|shrewd|shriven|shrunk|shrunken|shut|silvern|skint|slain|slept|slid|slit|slung|slunk|smelt|smitten|sold|sought|sown|spat|spelt|spent|spilt|spit|spoilt|spoken|spread|sprung|spun|stolen|stood|stove|strewn|struck|stuck|stung|stunk|sung|sunk|sunken|swept|swollen|sworn|swum|swung|taken|taught|thought|thrown|thrust|told|torn|trod|trodden|understood|unladen|unsold|untrodden|upheld|upset|wept|woken|won|worn|would|wound|woven|written|wrought|wrung',
    'beVerb' => "is|be|are",
    'linkVerb' => "[:activeLinkVerb:]|[:passiveLinkVerb:]",
    'realVerb' => '(join|connect|bond|attach|link|(re)?act|obtain|form|administer|protect)(ed)?|(fuse|derive|couple|incorporate|combine|prepare|use|recite|coordinate)d?|bound|taken|take|set|applied|apply',

    'RomanDigit' => 'v?i+|i?[vx]',
    'GreekNumber' => 'mono|di|tri|tetra|penta|hexa|hepta|octa|nona|deca|poly',
    'prefix' => 'non|anti|[:GreekNumber:]',
    
    'activeLinkVerb' => '(represent|denote|designate|indicate|equal|mean|stand)s?|signifies|signify',
    'passiveLinkVerb' => '(select|represent|defin|substitut|replac|elect)ed|chosen',
    
    
    'chemSymbol' => '[ABEGJLMQRWXYZ]',
    'chemSelect' => '[:activeLinkVerb:]|(?<=\b[:beVerb:][\xb7\xb8]+((as|not)[\xb7\xb8]+)?)[:passiveLinkVerb:]|[:beVerb:](?!([\xb7\xb8]+(as|not))?[\xb7\xb8]+[:participle:]\b)',
    "chemAtom" => "(deuterium|tritium|hydrogen|helium|lithium|beryllium|boron|carbon|nitrogen|oxygen|fluorine|neon|sodium|magnesium|aluminium|silicon|phosphorus|sulphur|sulfur|chlorine|argon|potassium|calcium|scandium|titanium|vanadium|chromium|manganese|iron|cobalt|nickel|copper|zinc|gallium|germanium|arsenic|selenium|bromine|krypton|rubidium|strontium|yttrium|zirconium|niobium|molybdenum|technetium|ruthenium|rhodium|palladium|silver|cadmium|indium|tin|antimony|tellurium|iodine|xenon|cesium|barium|lanthanum|cerium|praseodymium|neodymium|promethium|samarium|europium|gadolinium|terbium|dysprosium|holmium|erbium|thulium|ytterbium|lutetium|hafnium|tantalum|tungsten|rhenium|osmium|iridium|platinum|gold|mercury|thallium|lead|bismuth|polonium|astatine|radon|francium|radium|actinium|thorium|protactinium|uranium|neptunium|plutonium|americium|curium|berkelium|californium|einsteinium|fermium|mendelevium|nobelium|lawrencium)s?",
    "chemAtomAbbr" => "He|Li|Be|Ne|Na|Mg|Al|Si|Cl|Ar|Ca|Sc|Ti|Cr|Mn|Fe|Co|Ni|Cu|Zn|Ga|Ge|As|Se|Br|Kr|Rb|Sr|Zr|Nb|Mo|Tc|Ru|Rh|Pd|Ag|Cd|In|Sn|Sb|Te|Xe|Cs|Ba|La|Ce|Pr|Nd|Pm|Sm|Eu|Gd|Tb|Dy|Ho|Er|Tm|Yb|Lu|Hf|Ta|Re|Os|Ir|Pt|Au|Hg|Tl|Pb|Bi|Po|At|Rn|Fr|Ra|Ac|Th|Pa|Np|Pu|Am|Cm|Bk|Cf|Es|Fm|Md|No|Lr|H|D|T|B|C|N|O|F|P|S|K|V|Y|I|W|U",
    'chemGroup' => '[≡═—–-]|(hetero|alk|ary|meth(?!od)|halo|buty|cyan|prop|amid|hydro|cyclo)[a-z]+|[a-z]+(yl|ox[yo]|dine|atin|rine|lene|thio|ino|oro|romo|alo)|(?!centroid)[a-z]+[^v]oid',
    'chemFormula' => '([:chemAtomAbbr:]\d*|[:chemSymbol:]\d*[\'"′″*]*)+',
    'chemType' => '(group|ring|radical|chain|ligand|compound|cation|anion|atom|bond|spacer|structure|element|salt|acid|substituent|system|composition|substitution)s?|moiety|moieties|formulae?',
    'chemEntity' => "[:chemGroup:]|[:chemType:]|[:chemAtom:]|[:chemFormula:]|★",

    'chemHolderText' => '[:chemSymbol:](<(sup|sub)>\w+\s*</(sup|sub)>|\d*)[\'"′″*]*',
    'chemHolders' => '[:chemHolderText:]|[:chemSymbol:]<(sup|sub)>\d+\s*</(sup|sub)> *([—–-] *|to +)[:chemSymbol:]<(sup|sub)>\d+\s*</(sup|sub)>|[:chemSymbol:]\d+( *[—–-] *| +to +)[:chemSymbol:]\d+',
];

foreach ($wordClass as &$expr) {
    $expr = remove_capture($expr);
    $expr = "(?:$expr)";
}

function functional_substitution($s){
    global $wordClass;
    while (preg_match("/(?<![\\\\])\\[:[A-Za-z]+:\\]/", $s)) {
        $s = preg_replace_callback("/(?<![\\\\])\\[:([A-Za-z]+):\\]/", fn(&$m) => $wordClass[$m[1]], $s);
    }
    
    return $s;
}

?>