import sys, json, os, re, subprocess
from piper import PiperVoice, SynthesisConfig
import imageio_ffmpeg
FF = imageio_ffmpeg.get_ffmpeg_exe()

LENGTH_SCALE = 1.20      # Piper's default reads at ~193 wpm; this lands near 160

def synth(voice, paras, out_mp3, para_ms=560, sent_ms=190):
    cfg = SynthesisConfig(length_scale=LENGTH_SCALE)
    rate = voice.config.sample_rate
    sil_para = b'\x00\x00' * int(rate * para_ms / 1000)
    sil_sent = b'\x00\x00' * int(rate * sent_ms / 1000)
    pcm = bytearray()
    for p in paras:
        for s in (re.findall(r'[^.!?:;]+[.!?:;]*\s*', p) or [p]):
            s = s.strip()
            if not re.search(r'[A-Za-z0-9]', s):     # a stray quote synthesises to nothing
                continue
            got = False
            for chunk in voice.synthesize(s, syn_config=cfg):
                pcm += chunk.audio_int16_bytes; got = True
            if got:
                pcm += sil_sent
        pcm += sil_para
    subprocess.run([FF, '-y', '-loglevel', 'error', '-f', 's16le', '-ar', str(rate), '-ac', '1',
                    '-i', 'pipe:0', '-codec:a', 'libmp3lame', '-b:a', '64k', out_mp3],
                   input=bytes(pcm), check=True)
    return len(pcm) / 2 / rate

if __name__ == '__main__':
    model, outfile = sys.argv[1], sys.argv[2]
    parts = sys.argv[3].split(',') if len(sys.argv) > 3 else None
    D = json.load(open('script.json'))
    paras = [x['s'] for x in D['items'] if x['k'] == 'say' and (parts is None or x.get('p') in parts)]
    words = sum(len(p.split()) for p in paras)
    v = PiperVoice.load(model)
    secs = synth(v, paras, outfile)
    print('%s  %d paragraphs  %.1f s  (%.0f wpm)' % (outfile, len(paras), secs, words / (secs/60)))
