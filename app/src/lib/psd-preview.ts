/**
 * Minimal PSD/PSB parser for extracting a composite preview image as PNG.
 *
 * Ported from the PSD file structure described in psd-tools
 * (https://github.com/psd-tools/psd-tools, MIT licence).
 *
 * Supports:
 *  - PSD (version 1) and PSB (version 2)
 *  - 8-bit RGB, Grayscale, and CMYK color modes
 *  - RAW, RLE (PackBits), ZIP, and ZIP-with-prediction compression
 *  - JPEG thumbnail fallback from Image Resources (resource 1036)
 */

import * as Path from 'path'
import { readFile } from 'fs/promises'
import { deflateSync, inflateSync } from 'zlib'

// ─── constants ──────────────────────────────────────────────────────────────

const PSD_SIGNATURE = 0x38425053 // "8BPS"
const RESOURCE_BLOCK_SIGNATURE = 0x3842494d // "8BIM"
const THUMBNAIL_RESOURCE_ID = 1036
const THUMBNAIL_RESOURCE_PS4_ID = 1033

const MAX_COMPOSITE_PIXELS = 16_777_216 // 4096×4096

const enum Compression {
  RAW = 0,
  RLE = 1,
  ZIP = 2,
  ZIP_WITH_PREDICTION = 3,
}

const enum ColorMode {
  BITMAP = 0,
  GRAYSCALE = 1,
  INDEXED = 2,
  RGB = 3,
  CMYK = 4,
  MULTICHANNEL = 7,
  DUOTONE = 8,
  LAB = 9,
}

const psdExtensions = new Set(['.psd', '.psb'])

// ─── public helpers ─────────────────────────────────────────────────────────

export function isPSDExtension(filePath: string): boolean {
  return psdExtensions.has(Path.extname(filePath).toLowerCase())
}

// ─── CRC-32 for PNG ─────────────────────────────────────────────────────────

const CRC_TABLE = new Uint32Array(256)
for (let n = 0; n < 256; n++) {
  let c = n
  for (let k = 0; k < 8; k++) {
    c = c & 1 ? 0xedb88320 ^ (c >>> 1) : c >>> 1
  }
  CRC_TABLE[n] = c
}

function crc32(data: Buffer): number {
  let crc = 0xffffffff
  for (let i = 0; i < data.length; i++) {
    crc = CRC_TABLE[(crc ^ data[i]) & 0xff] ^ (crc >>> 8)
  }
  return (crc ^ 0xffffffff) >>> 0
}

// ─── minimal PNG encoder ────────────────────────────────────────────────────

function pngChunk(type: string, data: Buffer): Buffer {
  const typeBytes = Buffer.from(type, 'ascii')
  const len = Buffer.alloc(4)
  len.writeUInt32BE(data.length)
  const crcBuf = Buffer.alloc(4)
  crcBuf.writeUInt32BE(crc32(Buffer.concat([typeBytes, data])))
  return Buffer.concat([len, typeBytes, data, crcBuf])
}

function encodePNG(rgba: Uint8Array, width: number, height: number): Buffer {
  const rowLen = width * 4
  const filtered = Buffer.alloc(height * (1 + rowLen))
  for (let y = 0; y < height; y++) {
    const destRow = y * (1 + rowLen)
    filtered[destRow] = 0 // filter type None
    const srcOff = y * rowLen
    for (let x = 0; x < rowLen; x++) {
      filtered[destRow + 1 + x] = rgba[srcOff + x]
    }
  }

  const compressed = deflateSync(filtered)

  const signature = Buffer.from([137, 80, 78, 71, 13, 10, 26, 10])
  const ihdr = Buffer.alloc(13)
  ihdr.writeUInt32BE(width, 0)
  ihdr.writeUInt32BE(height, 4)
  ihdr.writeUInt8(8, 8) // bit depth
  ihdr.writeUInt8(6, 9) // color type RGBA
  ihdr.writeUInt8(0, 10) // compression
  ihdr.writeUInt8(0, 11) // filter
  ihdr.writeUInt8(0, 12) // interlace

  return Buffer.concat([
    signature,
    pngChunk('IHDR', ihdr),
    pngChunk('IDAT', compressed),
    pngChunk('IEND', Buffer.alloc(0)),
  ])
}

// ─── PSD header ─────────────────────────────────────────────────────────────

interface PSDHeader {
  version: number // 1 = PSD, 2 = PSB
  channels: number
  height: number
  width: number
  depth: number
  colorMode: number
}

function parseHeader(buf: Buffer): PSDHeader {
  if (buf.length < 26) {
    throw new Error('File too small for a PSD header')
  }
  if (buf.readUInt32BE(0) !== PSD_SIGNATURE) {
    throw new Error('Not a PSD/PSB file')
  }
  return {
    version: buf.readUInt16BE(4),
    channels: buf.readUInt16BE(12),
    height: buf.readUInt32BE(14),
    width: buf.readUInt32BE(18),
    depth: buf.readUInt16BE(22),
    colorMode: buf.readUInt16BE(24),
  }
}

// ─── PackBits RLE decoder (ported from psd-tools rle.py) ────────────────────

function decodePackBits(data: Buffer, offset: number, size: number, expectedLen: number): Buffer {
  const result = Buffer.alloc(expectedLen)
  let i = offset
  let j = 0
  const end = offset + size

  while (i < end && j < expectedLen) {
    const n = data.readInt8(i++)
    if (n >= 0) {
      const count = Math.min(n + 1, expectedLen - j, end - i)
      data.copy(result, j, i, i + count)
      j += count
      i += n + 1
    } else if (n !== -128) {
      const count = Math.min(-n + 1, expectedLen - j)
      if (i < end) {
        result.fill(data[i++], j, j + count)
        j += count
      }
    }
  }
  return result
}

// ─── thumbnail extraction from Image Resources ─────────────────────────────

interface ThumbnailData {
  data: Buffer
  width: number
  height: number
  isJPEG: boolean
}

function extractThumbnail(buf: Buffer): ThumbnailData | null {
  if (buf.length < 26) {
    return null
  }

  let offset = 26

  // skip Color Mode Data
  if (offset + 4 > buf.length) {
    return null
  }
  offset += 4 + buf.readUInt32BE(offset)

  // read Image Resources length
  if (offset + 4 > buf.length) {
    return null
  }
  const irLen = buf.readUInt32BE(offset)
  offset += 4
  const irEnd = offset + irLen

  while (offset + 12 <= irEnd && offset + 12 <= buf.length) {
    const sig = buf.readUInt32BE(offset)
    offset += 4
    if (sig !== RESOURCE_BLOCK_SIGNATURE) {
      break
    }

    const resId = buf.readUInt16BE(offset)
    offset += 2

    // pascal string (1-byte length + string + padding to even)
    const nameLen = buf.readUInt8(offset)
    const padded = nameLen + 1 + ((nameLen + 1) % 2)
    offset += padded

    if (offset + 4 > buf.length) {
      break
    }
    const dataLen = buf.readUInt32BE(offset)
    offset += 4

    if (
      resId === THUMBNAIL_RESOURCE_ID ||
      resId === THUMBNAIL_RESOURCE_PS4_ID
    ) {
      // thumbnail header: fmt(4) width(4) height(4) row(4) totalSize(4) size(4) bits(2) planes(2) = 28 bytes
      if (offset + 28 > buf.length) {
        break
      }
      const fmt = buf.readUInt32BE(offset)
      const tw = buf.readUInt32BE(offset + 4)
      const th = buf.readUInt32BE(offset + 8)
      const thumbSize = buf.readUInt32BE(offset + 20)
      const thumbStart = offset + 28

      if (thumbStart + thumbSize > buf.length) {
        break
      }
      return {
        data: Buffer.from(buf.subarray(thumbStart, thumbStart + thumbSize)),
        width: tw,
        height: th,
        isJPEG: fmt === 1,
      }
    }

    // skip resource data (padded to even)
    offset += dataLen + (dataLen % 2)
  }

  return null
}

// ─── composite image extraction ─────────────────────────────────────────────

function extractCompositeRGBA(
  buf: Buffer
): { data: Uint8Array; width: number; height: number } | null {
  const header = parseHeader(buf)
  const isPSB = header.version === 2

  if (header.depth !== 8) {
    return null
  }
  if (
    header.colorMode !== ColorMode.RGB &&
    header.colorMode !== ColorMode.GRAYSCALE &&
    header.colorMode !== ColorMode.CMYK
  ) {
    return null
  }

  const totalPixels = header.width * header.height
  if (totalPixels > MAX_COMPOSITE_PIXELS || totalPixels === 0) {
    return null
  }

  let offset = 26

  // skip Color Mode Data
  if (offset + 4 > buf.length) {
    return null
  }
  offset += 4 + buf.readUInt32BE(offset)

  // skip Image Resources
  if (offset + 4 > buf.length) {
    return null
  }
  offset += 4 + buf.readUInt32BE(offset)

  // skip Layer and Mask Info
  if (isPSB) {
    if (offset + 8 > buf.length) {
      return null
    }
    const high = buf.readUInt32BE(offset)
    const low = buf.readUInt32BE(offset + 4)
    offset += 8 + high * 0x100000000 + low
  } else {
    if (offset + 4 > buf.length) {
      return null
    }
    offset += 4 + buf.readUInt32BE(offset)
  }

  // Image Data section
  if (offset + 2 > buf.length) {
    return null
  }
  const compression: Compression = buf.readUInt16BE(offset)
  offset += 2

  const channelCount = header.channels
  const totalScanlines = header.height * channelCount

  let channelPlanes: Buffer[]

  try {
    switch (compression) {
      case Compression.RAW: {
        channelPlanes = []
        for (let c = 0; c < channelCount; c++) {
          if (offset + totalPixels > buf.length) {
            return null
          }
          channelPlanes.push(
            Buffer.from(buf.subarray(offset, offset + totalPixels))
          )
          offset += totalPixels
        }
        break
      }

      case Compression.RLE: {
        const bytesPerCount = isPSB ? 4 : 2
        if (offset + totalScanlines * bytesPerCount > buf.length) {
          return null
        }

        const scanlineCounts: number[] = []
        for (let i = 0; i < totalScanlines; i++) {
          scanlineCounts.push(
            isPSB
              ? buf.readUInt32BE(offset)
              : buf.readUInt16BE(offset)
          )
          offset += bytesPerCount
        }

        channelPlanes = []
        let scanIdx = 0
        for (let c = 0; c < channelCount; c++) {
          const planeBufs: Buffer[] = []
          for (let y = 0; y < header.height; y++) {
            const lineLen = scanlineCounts[scanIdx++]
            if (offset + lineLen > buf.length) {
              return null
            }
            planeBufs.push(
              decodePackBits(buf, offset, lineLen, header.width)
            )
            offset += lineLen
          }
          channelPlanes.push(Buffer.concat(planeBufs))
        }
        break
      }

      case Compression.ZIP:
      case Compression.ZIP_WITH_PREDICTION: {
        const remaining = buf.subarray(offset)
        const decompressed = inflateSync(remaining)
        const planeSize = totalPixels

        channelPlanes = []
        let chanOff = 0
        for (let c = 0; c < channelCount; c++) {
          if (chanOff + planeSize > decompressed.length) {
            return null
          }
          channelPlanes.push(
            Buffer.from(decompressed.subarray(chanOff, chanOff + planeSize))
          )
          chanOff += planeSize
        }

        if (compression === Compression.ZIP_WITH_PREDICTION) {
          for (const plane of channelPlanes) {
            for (let y = 0; y < header.height; y++) {
              const rowStart = y * header.width
              for (let x = 1; x < header.width; x++) {
                plane[rowStart + x] =
                  (plane[rowStart + x] + plane[rowStart + x - 1]) & 0xff
              }
            }
          }
        }
        break
      }

      default:
        return null
    }
  } catch {
    return null
  }

  // convert channel planes to interleaved RGBA
  const rgba = new Uint8Array(totalPixels * 4)

  if (header.colorMode === ColorMode.RGB) {
    const r = channelPlanes[0]
    const g = channelPlanes[1]
    const b = channelPlanes[2]
    const a = channelCount >= 4 ? channelPlanes[3] : null
    for (let i = 0; i < totalPixels; i++) {
      const o = i * 4
      rgba[o] = r[i]
      rgba[o + 1] = g[i]
      rgba[o + 2] = b[i]
      rgba[o + 3] = a ? a[i] : 255
    }
  } else if (header.colorMode === ColorMode.GRAYSCALE) {
    const l = channelPlanes[0]
    const a = channelCount >= 2 ? channelPlanes[1] : null
    for (let i = 0; i < totalPixels; i++) {
      const o = i * 4
      rgba[o] = l[i]
      rgba[o + 1] = l[i]
      rgba[o + 2] = l[i]
      rgba[o + 3] = a ? a[i] : 255
    }
  } else if (header.colorMode === ColorMode.CMYK) {
    const c = channelPlanes[0]
    const m = channelPlanes[1]
    const y = channelPlanes[2]
    const k = channelPlanes[3]
    const alpha = channelCount >= 5 ? channelPlanes[4] : null
    for (let i = 0; i < totalPixels; i++) {
      const o = i * 4
      const kk = k[i] / 255
      rgba[o] = Math.round(255 * (1 - c[i] / 255) * (1 - kk))
      rgba[o + 1] = Math.round(255 * (1 - m[i] / 255) * (1 - kk))
      rgba[o + 2] = Math.round(255 * (1 - y[i] / 255) * (1 - kk))
      rgba[o + 3] = alpha ? alpha[i] : 255
    }
  }

  return { data: rgba, width: header.width, height: header.height }
}

// ─── public API ─────────────────────────────────────────────────────────────

/**
 * Extract a PNG preview from a PSD/PSB buffer.
 *
 * Strategy:
 *  1. Try to decode the full composite image data (best quality).
 *  2. Fall back to the embedded JPEG thumbnail in Image Resources.
 *
 * Returns `{ png, mediaType }` — always `image/png` when composite
 * extraction succeeds, or `image/jpeg` when only the thumbnail is
 * available.
 */
export function getPSDPreview(
  buf: Buffer
): { data: Buffer; mediaType: string } {
  // 1. composite → PNG
  const composite = extractCompositeRGBA(buf)
  if (composite) {
    return {
      data: encodePNG(composite.data, composite.width, composite.height),
      mediaType: 'image/png',
    }
  }

  // 2. thumbnail fallback
  const thumb = extractThumbnail(buf)
  if (thumb && thumb.isJPEG) {
    return { data: thumb.data, mediaType: 'image/jpeg' }
  }

  throw new Error('No preview available for this PSD/PSB file')
}

export async function getPSDPreviewFromPath(
  filePath: string
): Promise<{ data: Buffer; mediaType: string }> {
  const buf = await readFile(filePath)
  return getPSDPreview(buf)
}
