# current directory: sh
source common.sh

src=$(normalize $1)
echo src = $src

dst=$(normalize $2)
echo dst = $dst

cd ../

srcFile=Axiom/${src//.//}.lean
echo srcFile = $srcFile

dstFile=Axiom/${dst//.//}.lean
echo dstFile = $dstFile

parent_path=$(dirname $dstFile)
echo mkdir -p $parent_path
mkdir -p $parent_path

echo mv $srcFile $dstFile
if [ -f $dstFile ]; then
    echo "error: $dstFile already exists"
    exit
fi
if [ ! -f $srcFile ]; then
    echo "error: $srcFile does not exist"
    exit
fi

mv $srcFile $dstFile

src_namespace=${src%.*}
src_namespace=${src_namespace//./\\.}
echo src_namespace = $src_namespace

dst_namespace=${dst%.*}
echo dst_namespace = $dst_namespace

src_theorem=${src##*.}
echo "src_theorem = $src_theorem"

dst_theorem=${dst##*.}
echo "dst_theorem = $dst_theorem"

srcReg=${src//./\\.}
echo srcReg = $srcReg
symm="(symm|mpr|mp)"
echo find Axiom -type f -name "*.lean" -exec sed -i -E "s/$srcReg([^.]|\.$symm|$)/$dst\1/g" {} +
find Axiom -type f -name "*.lean" -exec sed -i -E "s/$srcReg([^.]|\.$symm|$)/$dst\1/g" {} +

package=$(echo $src | cut -d'.' -f1)
echo package = $package

package_=$(echo $dst | cut -d'.' -f1)
echo package_ = $package_

if [ $package != $package_ ]; then
    echo "error: package names do not match"
    exit
fi

subNameSrc=$(echo "$src" | cut -d'.' -f2-)
subNameSrc=${subNameSrc//./\\.}
echo subNameSrc = $subNameSrc

subNameDst=$(echo "$dst" | cut -d'.' -f2-)
echo subNameDst = $subNameDst

find Axiom -type f -name "*.lean" | xargs grep -lE "(open( [[:alnum:]_.]+)*|namespace) $package" | xargs sed -i -E "s/$subNameSrc([^.]|\.$symm|$)/$subNameDst\1/g"