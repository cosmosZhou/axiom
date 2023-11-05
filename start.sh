#!/bin/bash
# usage:
# sh start.sh --tcp=2000 --workers=4 --worker-class=gevent
# pip install gunicorn flask

directory=$(dirname $0)

if [ "$directory" != "." ]; then
    echo directory = $directory
    echo current directory is not the default directory! setting pwd = $directory
    cd $directory && sh $(basename $0) $*
    exit
fi

rm -f *.lock

#!/bin/bash  
  
options="app: tcp: workers: worker-class: password: timeout: cuda: gpu_count: log_level: threads: kill tail pstree"  
  
PARSED_OPTIONS=$(getopt -o h --long "$options" -- "$@")  
  
if [ $? -ne 0 ]; then  
    echo "Error parsing options"  
    exit 1  
fi  
  
eval set -- "$PARSED_OPTIONS"  
while true; do  
    case "$1" in  
        --workers)
            workers="$2"
            shift 2
            ;;
        --tcp)
            tcp="$2"
            shift 2    
            ;;
        --worker-class)
            worker_class="$2"
            shift 2
            ;;
        --app)
            app="$2"
            shift 2
            ;;                
        --password)
            password="$2"
            shift 2
            ;;        
        --timeout)
            timeout="$2"
            shift 2
            ;;
        --cuda)
            CUDA_VISIBLE_DEVICES="$2"
            shift 2
            ;;
        --gpu_count)
            gpu_count="$2"
            shift 2
            ;;
        --log_level)
            log_level="$2"
            shift 2
            ;;   
        --threads)
            threads="$2"
            shift 2
            ;;   
    
        --kill)
            cmd_kill=1
            shift
            ;;
        --tail)
            tail -100f error.log
            exit
            ;;
        --pstree)
            pstree -ap | grep gunicorn | grep -v grep
            exit
            ;;
        --)
            shift  
            break  
            ;;  
        *)
            echo "Error parsing options"  
            exit 1
            ;;  
    esac  
done  
  
if [ -z "$workers" ]; then
    workers=8
    echo set workers=$workers by default!
fi

if [ -z "$tcp" ]; then
    tcp=5000
    echo set tcp=$tcp by default!
fi

if [ -z "$worker_class" ]; then
    worker_class=sync
    echo set worker_class=$worker_class by default!
fi

if [ -z "$threads" ]; then
    threads=1
    echo set threads=threads by default!
fi

if [ -z "$timeout" ]; then
    timeout=86400
    echo set timeout=$timeout by default!
fi

if [ -z "$app" ]; then
    app=main
    echo set app=$app by default!
fi

if [ -z "$log_level" ]; then
    log_level=error
    echo set log_level=$log_level by default!
fi

if [ -z "$CUDA_VISIBLE_DEVICES" ]; then
    if [ -z "$gpu_count" ]; then
        CUDA_VISIBLE_DEVICES=-1
        echo set CUDA_VISIBLE_DEVICES=$CUDA_VISIBLE_DEVICES by default!
    fi
fi

echo -e "\n\n"
echo workers = $workers
echo tcp = $tcp
echo worker_class = $worker_class
echo app = $app
echo password = $password
echo timeout = $timeout

echo lsof -i tcp:$tcp
lsof -i tcp:$tcp

echo "lsof -i tcp:$tcp | awk '{if (NR > 1) print \$2}'"
lsof -i tcp:$tcp | awk '{if (NR > 1) print $2}'
array=($(lsof -i tcp:$tcp | awk '{if (NR > 1) print $2}'))

for pid in ${array[*]}; do
    echo kill -9 $pid
    kill -9 $pid
done

if [ ! -z ${cmd_kill} ]; then
    exit
fi

create_log_file(){
    log=$1
    if [ ! -f "$log" ]; then
        echo touch $log
        touch $log
    else
        echo "ls -l $log | awk '{print \$5}'"
        ls -l $log | awk '{print $5}'
        getsize=$(ls -l $log | awk '{print $5}')
        echo getsize = $getsize
        
        getsize=$[getsize / 1024 / 1024]
        echo getsize / 1024 / 1024 = $getsize
        
        if [ $getsize -gt 30 ]; then            
            echo $log file is larger than 30M, shrinking to 0M
            echo > $log
        fi
    fi    
}

create_log_file access.log
create_log_file error.log

git pull

start="gunicorn --workers=$workers \
                --bind=0.0.0.0:$tcp \
                --daemon \
                --timeout=$timeout \
                --access-logfile=access.log \
                --error-logfile=error.log \
                --log-level=$log_level \
                --capture-output \
                --worker-class=$worker_class \
                $app:app"
             
if [ ! "$CUDA_VISIBLE_DEVICES" ]; then
    export gpu_count=$gpu_count && ${start}
else
    export CUDA_VISIBLE_DEVICES=$CUDA_VISIBLE_DEVICES && ${start}
fi

echo $start
tail -100f error.log