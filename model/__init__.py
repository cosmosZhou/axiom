import os
os.environ['MYSQL_HOST'] = '192.168.18.132'
os.environ['MYSQL_DATABASE'] = 'axiom'

from std.keras import set_cuda_visible_devices
set_cuda_visible_devices()